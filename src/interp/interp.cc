/*
 * Copyright 2020 WebAssembly Community Group participants
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "src/interp/interp.h"

#include <algorithm>
#include <cassert>
#include <cinttypes>

#include "src/interp/interp-math.h"
#include "src/make-unique.h"

namespace wabt {
namespace interp {

const char* GetName(Mutability mut) {
  static const char* kNames[] = {"immutable", "mutable"};
  return kNames[int(mut)];
}

const std::string GetName(ValueType type) {
  return type.GetName();
}

const char* GetName(ExternKind kind) {
  return GetKindName(kind);
}

const char* GetName(ObjectKind kind) {
  static const char* kNames[] = {
      "Null",  "Foreign", "Trap",   "Exception", "DefinedFunc", "HostFunc",
      "Table", "Memory",  "Global", "Tag",       "Module",      "Instance",
  };

  WABT_STATIC_ASSERT(WABT_ARRAY_SIZE(kNames) == kCommandTypeCount);

  return kNames[int(kind)];
}

//// Refs ////
// static
const Ref Ref::Null{0};

//// Limits ////
Result Match(const Limits& expected,
             const Limits& actual,
             std::string* out_msg) {
  if (actual.initial < expected.initial) {
    *out_msg = StringPrintf("actual size (%" PRIu64
                            ") smaller than declared (%" PRIu64 ")",
                            actual.initial, expected.initial);
    return Result::Error;
  }

  if (expected.has_max) {
    if (!actual.has_max) {
      *out_msg = StringPrintf(
          "max size (unspecified) larger than declared (%" PRIu64 ")",
          expected.max);
      return Result::Error;
    } else if (actual.max > expected.max) {
      *out_msg = StringPrintf("max size (%" PRIu64
                              ") larger than declared (%" PRIu64 ")",
                              actual.max, expected.max);
      return Result::Error;
    }
  }

  return Result::Ok;
}

//// FuncType ////
std::unique_ptr<ExternType> FuncType::Clone() const {
  return MakeUnique<FuncType>(*this);
}

Result Match(const FuncType& expected,
             const FuncType& actual,
             std::string* out_msg) {
  if (expected.params != actual.params || expected.results != actual.results) {
    if (out_msg) {
      *out_msg = "import signature mismatch";
    }
    return Result::Error;
  }
  return Result::Ok;
}

//// TableType ////
std::unique_ptr<ExternType> TableType::Clone() const {
  return MakeUnique<TableType>(*this);
}

Result Match(const TableType& expected,
             const TableType& actual,
             std::string* out_msg) {
  if (expected.element != actual.element) {
    *out_msg = StringPrintf(
        "type mismatch in imported table, expected %s but got %s.",
        GetName(expected.element).c_str(), GetName(actual.element).c_str());
    return Result::Error;
  }

  if (Failed(Match(expected.limits, actual.limits, out_msg))) {
    return Result::Error;
  }

  return Result::Ok;
}

//// MemoryType ////
std::unique_ptr<ExternType> MemoryType::Clone() const {
  return MakeUnique<MemoryType>(*this);
}

Result Match(const MemoryType& expected,
             const MemoryType& actual,
             std::string* out_msg) {
  return Match(expected.limits, actual.limits, out_msg);
}

//// GlobalType ////
std::unique_ptr<ExternType> GlobalType::Clone() const {
  return MakeUnique<GlobalType>(*this);
}

Result Match(const GlobalType& expected,
             const GlobalType& actual,
             std::string* out_msg) {
  if (actual.mut != expected.mut) {
    *out_msg = StringPrintf(
        "mutability mismatch in imported global, expected %s but got %s.",
        GetName(actual.mut), GetName(expected.mut));
    return Result::Error;
  }

  if (actual.type != expected.type &&
      (expected.mut == Mutability::Var ||
       !TypesMatch(expected.type, actual.type))) {
    *out_msg = StringPrintf(
        "type mismatch in imported global, expected %s but got %s.",
        GetName(expected.type).c_str(), GetName(actual.type).c_str());
    return Result::Error;
  }

  return Result::Ok;
}

//// TagType ////
std::unique_ptr<ExternType> TagType::Clone() const {
  return MakeUnique<TagType>(*this);
}

Result Match(const TagType& expected,
             const TagType& actual,
             std::string* out_msg) {
  if (expected.signature != actual.signature) {
    if (out_msg) {
      *out_msg = "signature mismatch in imported tag";
    }
    return Result::Error;
  }
  return Result::Ok;
}

//// Limits ////
template <typename T>
bool CanGrow(const Limits& limits, T old_size, T delta, T* new_size) {
  if (limits.max >= delta && old_size <= limits.max - delta) {
    *new_size = old_size + delta;
    return true;
  }
  return false;
}

//// FuncDesc ////

ValueType FuncDesc::GetLocalType(Index index) const {
  if (index < type.params.size()) {
    return type.params[index];
  }
  index -= type.params.size();

  auto iter = std::lower_bound(
      locals.begin(), locals.end(), index + 1,
      [](const LocalDesc& lhs, Index rhs) { return lhs.end < rhs; });
  assert(iter != locals.end());
  return iter->type;
}

//// Store ////
Store::Store(const Features& features) : features_(features) {
  Ref ref{objects_.New(new Object(ObjectKind::Null))};
  assert(ref == Ref::Null);
  roots_.New(ref);
}

bool Store::HasValueType(Ref ref, ValueType type) const {
  // TODO opt?
  if (!IsValid(ref)) {
    return false;
  }
  if (type == ValueType::ExternRef) {
    return true;
  }
  if (ref == Ref::Null) {
    return true;
  }

  Object* obj = objects_.Get(ref.index);
  switch (type) {
    case ValueType::FuncRef:
      return obj->kind() == ObjectKind::DefinedFunc ||
             obj->kind() == ObjectKind::HostFunc;
    default:
      return false;
  }
}

Store::RootList::Index Store::NewRoot(Ref ref) {
  return roots_.New(ref);
}

Store::RootList::Index Store::CopyRoot(RootList::Index index) {
  // roots_.Get() returns a reference to an element in an internal vector, and
  // roots_.New() might forward its arguments to emplace_back on the same
  // vector. This seems to "work" in most environments, but fails on Visual
  // Studio 2015 Win64. Copying it to a value fixes the issue.
  auto obj_index = roots_.Get(index);
  return roots_.New(obj_index);
}

void Store::DeleteRoot(RootList::Index index) {
  roots_.Delete(index);
}

void Store::Collect() {
  size_t object_count = objects_.size();

  assert(gc_context_.call_depth == 0);

  gc_context_.marks.resize(object_count);
  std::fill(gc_context_.marks.begin(), gc_context_.marks.end(), false);

  // First mark all roots.
  for (RootList::Index i = 0; i < roots_.size(); ++i) {
    if (roots_.IsUsed(i)) {
      Mark(roots_.Get(i));
    }
  }

  for (auto thread : threads_) {
    thread->Mark();
  }

  // This vector is often empty since the default maximum
  // recursion is usually enough to mark all objects.
  while (WABT_UNLIKELY(!gc_context_.untraced_objects.empty())) {
    size_t index = gc_context_.untraced_objects.back();

    assert(gc_context_.marks[index]);
    assert(gc_context_.call_depth == 0);

    gc_context_.untraced_objects.pop_back();
    objects_.Get(index)->Mark(*this);
  }

  assert(gc_context_.call_depth == 0);

  // Delete all unmarked objects.
  for (size_t i = 0; i < object_count; ++i) {
    if (objects_.IsUsed(i) && !gc_context_.marks[i]) {
      objects_.Delete(i);
    }
  }
}

void Store::Mark(Ref ref) {
  size_t index = ref.index;

  if (gc_context_.marks[index])
    return;

  gc_context_.marks[index] = true;

  if (WABT_UNLIKELY(gc_context_.call_depth >= max_call_depth)) {
    gc_context_.untraced_objects.push_back(index);
    return;
  }

  gc_context_.call_depth++;
  objects_.Get(index)->Mark(*this);
  gc_context_.call_depth--;
}

void Store::Mark(const RefVec& refs) {
  for (auto&& ref : refs) {
    Mark(ref);
  }
}

//// Object ////
Object::~Object() {
  if (finalizer_) {
    finalizer_(this);
  }
}

//// Foreign ////
Foreign::Foreign(Store&, void* ptr) : Object(skind), ptr_(ptr) {}

void Foreign::Mark(Store&) {}

//// Frame ////
void Frame::Mark(Store& store) {
  store.Mark(func);
}

//// Trap ////
Trap::Trap(Store& store,
           const std::string& msg,
           const std::vector<Frame>& trace)
    : Object(skind), message_(msg), trace_(trace) {}

void Trap::Mark(Store& store) {
  for (auto&& frame : trace_) {
    frame.Mark(store);
  }
}

//// Exception ////
Exception::Exception(Store& store, Ref tag, Values& args)
    : Object(skind), tag_(tag), args_(args) {}

void Exception::Mark(Store& store) {
  Tag::Ptr tag(store, tag_);
  store.Mark(tag_);
  ValueTypes params = tag->type().signature;
  for (size_t i = 0; i < params.size(); i++) {
    if (params[i].IsRef()) {
      store.Mark(args_[i].Get<Ref>());
    }
  }
}

//// Extern ////
template <typename T>
Result Extern::MatchImpl(Store& store,
                         const ImportType& import_type,
                         const T& actual,
                         Trap::Ptr* out_trap) {
  const T* extern_type = dyn_cast<T>(import_type.type.get());
  if (!extern_type) {
    *out_trap = Trap::New(
        store,
        StringPrintf("expected import \"%s.%s\" to have kind %s, not %s",
                     import_type.module.c_str(), import_type.name.c_str(),
                     GetName(import_type.type->kind), GetName(T::skind)));
    return Result::Error;
  }

  std::string msg;
  if (Failed(interp::Match(*extern_type, actual, &msg))) {
    *out_trap = Trap::New(store, msg);
    return Result::Error;
  }

  return Result::Ok;
}

//// Func ////
Func::Func(ObjectKind kind, FuncType type) : Extern(kind), type_(type) {}

Result Func::Call(Store& store,
                  const Values& params,
                  Values& results,
                  Trap::Ptr* out_trap,
                  Stream* trace_stream) {
  Thread thread(store, trace_stream);
  return DoCall(thread, params, results, out_trap);
}

Result Func::Call(Thread& thread,
                  const Values& params,
                  Values& results,
                  Trap::Ptr* out_trap) {
  return DoCall(thread, params, results, out_trap);
}

//// DefinedFunc ////
DefinedFunc::DefinedFunc(Store& store, Ref instance, FuncDesc desc)
    : Func(skind, desc.type), instance_(instance), desc_(desc) {}

void DefinedFunc::Mark(Store& store) {
  store.Mark(instance_);
}

Result DefinedFunc::Match(Store& store,
                          const ImportType& import_type,
                          Trap::Ptr* out_trap) {
  return MatchImpl(store, import_type, type_, out_trap);
}

Result DefinedFunc::DoCall(Thread& thread,
                           const Values& params,
                           Values& results,
                           Trap::Ptr* out_trap) {
  assert(params.size() == type_.params.size());
  thread.PushValues(type_.params, params);
  RunResult result = thread.PushCall(*this, out_trap);
  if (result == RunResult::Trap) {
    return Result::Error;
  }
  result = thread.Run(out_trap);
  if (result == RunResult::Trap) {
    return Result::Error;
  } else if (result == RunResult::Exception) {
    // While this is not actually a trap, it is a convenient way
    // to report an uncaught exception.
    *out_trap = Trap::New(thread.store(), "uncaught exception");
    return Result::Error;
  }
  thread.PopValues(type_.results, &results);
  return Result::Ok;
}

//// HostFunc ////
HostFunc::HostFunc(Store&, FuncType type, Callback callback)
    : Func(skind, type), callback_(callback) {}

void HostFunc::Mark(Store&) {}

Result HostFunc::Match(Store& store,
                       const ImportType& import_type,
                       Trap::Ptr* out_trap) {
  return MatchImpl(store, import_type, type_, out_trap);
}

Result HostFunc::DoCall(Thread& thread,
                        const Values& params,
                        Values& results,
                        Trap::Ptr* out_trap) {
  return callback_(thread, params, results, out_trap);
}

//// Table ////
Table::Table(Store&, TableType type) : Extern(skind), type_(type) {
  elements_.resize(type.limits.initial);
}

void Table::Mark(Store& store) {
  store.Mark(elements_);
}

Result Table::Match(Store& store,
                    const ImportType& import_type,
                    Trap::Ptr* out_trap) {
  return MatchImpl(store, import_type, type_, out_trap);
}

bool Table::IsValidRange(u32 offset, u32 size) const {
  size_t elem_size = elements_.size();
  return size <= elem_size && offset <= elem_size - size;
}

Result Table::Get(u32 offset, Ref* out) const {
  if (IsValidRange(offset, 1)) {
    *out = elements_[offset];
    return Result::Ok;
  }
  return Result::Error;
}

Ref Table::UnsafeGet(u32 offset) const {
  assert(IsValidRange(offset, 1));
  return elements_[offset];
}

Result Table::Set(Store& store, u32 offset, Ref ref) {
  if (IsValidRange(offset, 1) && store.HasValueType(ref, type_.element)) {
    elements_[offset] = ref;
    return Result::Ok;
  }
  return Result::Error;
}

Result Table::Grow(Store& store, u32 count, Ref ref) {
  size_t old_size = elements_.size();
  u32 new_size;
  if (store.HasValueType(ref, type_.element) &&
      CanGrow<u32>(type_.limits, old_size, count, &new_size)) {
    // Grow the limits of the table too, so that if it is used as an
    // import to another module its new size is honored.
    type_.limits.initial += count;
    elements_.resize(new_size);
    Fill(store, old_size, ref, new_size - old_size);
    return Result::Ok;
  }
  return Result::Error;
}

Result Table::Fill(Store& store, u32 offset, Ref ref, u32 size) {
  if (IsValidRange(offset, size) && store.HasValueType(ref, type_.element)) {
    std::fill(elements_.begin() + offset, elements_.begin() + offset + size,
              ref);
    return Result::Ok;
  }
  return Result::Error;
}

Result Table::Init(Store& store,
                   u32 dst_offset,
                   const ElemSegment& src,
                   u32 src_offset,
                   u32 size) {
  if (IsValidRange(dst_offset, size) && src.IsValidRange(src_offset, size) &&
      TypesMatch(type_.element, src.desc().type)) {
    std::copy(src.elements().begin() + src_offset,
              src.elements().begin() + src_offset + size,
              elements_.begin() + dst_offset);
    return Result::Ok;
  }
  return Result::Error;
}

// static
Result Table::Copy(Store& store,
                   Table& dst,
                   u32 dst_offset,
                   const Table& src,
                   u32 src_offset,
                   u32 size) {
  if (dst.IsValidRange(dst_offset, size) &&
      src.IsValidRange(src_offset, size) &&
      TypesMatch(dst.type_.element, src.type_.element)) {
    auto src_begin = src.elements_.begin() + src_offset;
    auto src_end = src_begin + size;
    auto dst_begin = dst.elements_.begin() + dst_offset;
    auto dst_end = dst_begin + size;
    if (dst.self() == src.self() && src_begin < dst_begin) {
      std::move_backward(src_begin, src_end, dst_end);
    } else {
      std::move(src_begin, src_end, dst_begin);
    }
    return Result::Ok;
  }
  return Result::Error;
}

//// Memory ////
Memory::Memory(class Store&, MemoryType type)
    : Extern(skind), type_(type), pages_(type.limits.initial) {
  data_.resize(pages_ * WABT_PAGE_SIZE);
}

void Memory::Mark(class Store&) {}

Result Memory::Match(class Store& store,
                     const ImportType& import_type,
                     Trap::Ptr* out_trap) {
  return MatchImpl(store, import_type, type_, out_trap);
}

Result Memory::Grow(u64 count) {
  u64 new_pages;
  if (CanGrow<u64>(type_.limits, pages_, count, &new_pages)) {
    // Grow the limits of the memory too, so that if it is used as an
    // import to another module its new size is honored.
    type_.limits.initial += count;
#if WABT_BIG_ENDIAN
    auto old_size = data_.size();
#endif
    pages_ = new_pages;
    data_.resize(new_pages * WABT_PAGE_SIZE);
#if WABT_BIG_ENDIAN
    std::move_backward(data_.begin(), data_.begin() + old_size, data_.end());
    std::fill(data_.begin(), data_.end() - old_size, 0);
#endif
    return Result::Ok;
  }
  return Result::Error;
}

Result Memory::Fill(u64 offset, u8 value, u64 size) {
  if (IsValidAccess(offset, 0, size)) {
#if WABT_BIG_ENDIAN
    std::fill(data_.end() - offset - size, data_.end() - offset, value);
#else
    std::fill(data_.begin() + offset, data_.begin() + offset + size, value);
#endif
    return Result::Ok;
  }
  return Result::Error;
}

Result Memory::Init(u64 dst_offset,
                    const DataSegment& src,
                    u64 src_offset,
                    u64 size) {
  if (IsValidAccess(dst_offset, 0, size) &&
      src.IsValidRange(src_offset, size)) {
    std::copy(src.desc().data.begin() + src_offset,
              src.desc().data.begin() + src_offset + size,
#if WABT_BIG_ENDIAN
              data_.rbegin() + dst_offset);
#else
              data_.begin() + dst_offset);
#endif
    return Result::Ok;
  }
  return Result::Error;
}

// static
Result Memory::Copy(Memory& dst,
                    u64 dst_offset,
                    const Memory& src,
                    u64 src_offset,
                    u64 size) {
  if (dst.IsValidAccess(dst_offset, 0, size) &&
      src.IsValidAccess(src_offset, 0, size)) {
#if WABT_BIG_ENDIAN
    auto src_begin = src.data_.end() - src_offset - size;
    auto dst_begin = dst.data_.end() - dst_offset - size;
#else
    auto src_begin = src.data_.begin() + src_offset;
    auto dst_begin = dst.data_.begin() + dst_offset;
#endif
    auto src_end = src_begin + size;
    auto dst_end = dst_begin + size;
    if (src.self() == dst.self() && src_begin < dst_begin) {
      std::move_backward(src_begin, src_end, dst_end);
    } else {
      std::move(src_begin, src_end, dst_begin);
    }
    return Result::Ok;
  }
  return Result::Error;
}

Result Instance::CallInitFunc(Store& store,
                              const Ref func_ref,
                              Value* result,
                              Trap::Ptr* out_trap) {
  Values results;
  Func::Ptr func{store, func_ref};
  if (Failed(func->Call(store, {}, results, out_trap))) {
    return Result::Error;
  }
  assert(results.size() == 1);
  *result = results[0];
  return Result::Ok;
}

//// Global ////
Global::Global(Store& store, GlobalType type, Value value)
    : Extern(skind), type_(type), value_(value) {}

void Global::Mark(Store& store) {
  if (IsReference(type_.type)) {
    store.Mark(value_.Get<Ref>());
  }
}

Result Global::Match(Store& store,
                     const ImportType& import_type,
                     Trap::Ptr* out_trap) {
  return MatchImpl(store, import_type, type_, out_trap);
}

Result Global::Set(Store& store, Ref ref) {
  if (store.HasValueType(ref, type_.type)) {
    value_.Set(ref);
    return Result::Ok;
  }
  return Result::Error;
}

void Global::UnsafeSet(Value value) {
  value_ = value;
}

//// Tag ////
Tag::Tag(Store&, TagType type) : Extern(skind), type_(type) {}

void Tag::Mark(Store&) {}

Result Tag::Match(Store& store,
                  const ImportType& import_type,
                  Trap::Ptr* out_trap) {
  return MatchImpl(store, import_type, type_, out_trap);
}

//// ElemSegment ////
ElemSegment::ElemSegment(const ElemDesc* desc, Instance::Ptr& inst)
    : desc_(desc) {
  elements_.reserve(desc->elements.size());
  for (auto&& elem_expr : desc->elements) {
    switch (elem_expr.kind) {
      case ElemKind::RefNull:
        elements_.emplace_back(Ref::Null);
        break;

      case ElemKind::RefFunc:
        elements_.emplace_back(inst->funcs_[elem_expr.index]);
        break;
    }
  }
}

bool ElemSegment::IsValidRange(u32 offset, u32 size) const {
  u32 elem_size = this->size();
  return size <= elem_size && offset <= elem_size - size;
}

//// DataSegment ////
DataSegment::DataSegment(const DataDesc* desc)
    : desc_(desc), size_(desc->data.size()) {}

bool DataSegment::IsValidRange(u64 offset, u64 size) const {
  u64 data_size = size_;
  return size <= data_size && offset <= data_size - size;
}

//// Module ////
Module::Module(Store&, ModuleDesc desc)
    : Object(skind), desc_(std::move(desc)) {
  for (auto&& import : desc_.imports) {
    import_types_.emplace_back(import.type);
  }

  for (auto&& export_ : desc_.exports) {
    export_types_.emplace_back(export_.type);
  }
}

void Module::Mark(Store&) {}

//// ElemSegment ////
void ElemSegment::Mark(Store& store) {
  store.Mark(elements_);
}

//// Instance ////
Instance::Instance(Store& store, Ref module) : Object(skind), module_(module) {
  assert(store.Is<Module>(module));
}

// static
Instance::Ptr Instance::Instantiate(Store& store,
                                    Ref module,
                                    const RefVec& imports,
                                    Trap::Ptr* out_trap) {
  Module::Ptr mod{store, module};
  Instance::Ptr inst = store.Alloc<Instance>(store, module);

  size_t import_desc_count = mod->desc().imports.size();
  if (imports.size() < import_desc_count) {
    *out_trap = Trap::New(store, "not enough imports!");
    return {};
  }

  // Imports.
  for (size_t i = 0; i < import_desc_count; ++i) {
    auto&& import_desc = mod->desc().imports[i];
    Ref extern_ref = imports[i];
    if (extern_ref == Ref::Null) {
      *out_trap = Trap::New(store, StringPrintf("invalid import \"%s.%s\"",
                                                import_desc.type.module.c_str(),
                                                import_desc.type.name.c_str()));
      return {};
    }

    Extern::Ptr extern_{store, extern_ref};
    if (Failed(extern_->Match(store, import_desc.type, out_trap))) {
      return {};
    }

    inst->imports_.push_back(extern_ref);

    switch (import_desc.type.type->kind) {
      case ExternKind::Func:   inst->funcs_.push_back(extern_ref); break;
      case ExternKind::Table:  inst->tables_.push_back(extern_ref); break;
      case ExternKind::Memory: inst->memories_.push_back(extern_ref); break;
      case ExternKind::Global: inst->globals_.push_back(extern_ref); break;
      case ExternKind::Tag:    inst->tags_.push_back(extern_ref); break;
    }
  }

  // Funcs.
  for (auto&& desc : mod->desc().funcs) {
    inst->funcs_.push_back(DefinedFunc::New(store, inst.ref(), desc).ref());
  }

  // Tables.
  for (auto&& desc : mod->desc().tables) {
    inst->tables_.push_back(Table::New(store, desc.type).ref());
  }

  // Memories.
  for (auto&& desc : mod->desc().memories) {
    inst->memories_.push_back(Memory::New(store, desc.type).ref());
  }

  // Globals.
  for (auto&& desc : mod->desc().globals) {
    Value value;
    Ref func_ref = DefinedFunc::New(store, inst.ref(), desc.init_func).ref();
    if (Failed(inst->CallInitFunc(store, func_ref, &value, out_trap))) {
      return {};
    }
    inst->globals_.push_back(Global::New(store, desc.type, value).ref());
  }

  // Tags.
  for (auto&& desc : mod->desc().tags) {
    inst->tags_.push_back(Tag::New(store, desc.type).ref());
  }

  // Exports.
  for (auto&& desc : mod->desc().exports) {
    Ref ref;
    switch (desc.type.type->kind) {
      case ExternKind::Func:   ref = inst->funcs_[desc.index]; break;
      case ExternKind::Table:  ref = inst->tables_[desc.index]; break;
      case ExternKind::Memory: ref = inst->memories_[desc.index]; break;
      case ExternKind::Global: ref = inst->globals_[desc.index]; break;
      case ExternKind::Tag:    ref = inst->tags_[desc.index]; break;
    }
    inst->exports_.push_back(ref);
  }

  // Elems.
  for (auto&& desc : mod->desc().elems) {
    inst->elems_.emplace_back(&desc, inst);
  }

  // Datas.
  for (auto&& desc : mod->desc().datas) {
    inst->datas_.emplace_back(&desc);
  }

  // Initialization.
  // The MVP requires that all segments are bounds-checked before being copied
  // into the table or memory. The bulk memory proposal changes this behavior;
  // instead, each segment is copied in order. If any segment fails, then no
  // further segments are copied. Any data that was written persists.
  enum Pass { Check, Init };
  int pass = store.features().bulk_memory_enabled() ? Init : Check;
  for (; pass <= Init; ++pass) {
    // Elems.
    for (auto&& segment : inst->elems_) {
      auto&& desc = segment.desc();
      if (desc.mode == SegmentMode::Active) {
        Result result;
        Table::Ptr table{store, inst->tables_[desc.table_index]};
        Value value;
        Ref func_ref =
            DefinedFunc::New(store, inst.ref(), desc.init_func).ref();
        if (Failed(inst->CallInitFunc(store, func_ref, &value, out_trap))) {
          return {};
        }
        u32 offset = value.Get<u32>();
        if (pass == Check) {
          result = table->IsValidRange(offset, segment.size()) ? Result::Ok
                                                               : Result::Error;
        } else {
          result = table->Init(store, offset, segment, 0, segment.size());
          if (Succeeded(result)) {
            segment.Drop();
          }
        }

        if (Failed(result)) {
          *out_trap = Trap::New(
              store, StringPrintf(
                         "out of bounds table access: elem segment is "
                         "out of bounds: [%u, %" PRIu64 ") >= max value %u",
                         offset, u64{offset} + segment.size(), table->size()));
          return {};
        }
      } else if (desc.mode == SegmentMode::Declared) {
        segment.Drop();
      }
    }

    // Data.
    for (auto&& segment : inst->datas_) {
      auto&& desc = segment.desc();
      if (desc.mode == SegmentMode::Active) {
        Result result;
        Memory::Ptr memory{store, inst->memories_[desc.memory_index]};
        Value offset_op;
        Ref func_ref =
            DefinedFunc::New(store, inst.ref(), desc.init_func).ref();
        if (Failed(inst->CallInitFunc(store, func_ref, &offset_op, out_trap))) {
          return {};
        }
        u64 offset = memory->type().limits.is_64 ? offset_op.Get<u64>()
                                                 : offset_op.Get<u32>();
        if (pass == Check) {
          result = memory->IsValidAccess(offset, 0, segment.size())
                       ? Result::Ok
                       : Result::Error;
        } else {
          result = memory->Init(offset, segment, 0, segment.size());
          if (Succeeded(result)) {
            segment.Drop();
          }
        }

        if (Failed(result)) {
          *out_trap = Trap::New(
              store, StringPrintf(
                         "out of bounds memory access: data segment is "
                         "out of bounds: [%" PRIu64 ", %" PRIu64
                         ") >= max value %" PRIu64,
                         offset, offset + segment.size(), memory->ByteSize()));
          return {};
        }
      } else if (desc.mode == SegmentMode::Declared) {
        segment.Drop();
      }
    }
  }

  // Start.
  for (auto&& start : mod->desc().starts) {
    Func::Ptr func{store, inst->funcs_[start.func_index]};
    Values results;
    if (Failed(func->Call(store, {}, results, out_trap))) {
      return {};
    }
  }

  return inst;
}

void Instance::Mark(Store& store) {
  store.Mark(module_);
  store.Mark(imports_);
  store.Mark(funcs_);
  store.Mark(memories_);
  store.Mark(tables_);
  store.Mark(globals_);
  store.Mark(tags_);
  store.Mark(exports_);
  for (auto&& elem : elems_) {
    elem.Mark(store);
  }
}

//// Thread ////
Thread::Thread(Store& store, Stream* trace_stream)
    : store_(store), trace_stream_(trace_stream) {
  store.threads().insert(this);

  Thread::Options options;
  frames_.reserve(options.call_stack_size);
  values_.reserve(options.value_stack_size);
  if (trace_stream) {
    trace_source_ = MakeUnique<TraceSource>(this);
  }
}

Thread::~Thread() {
  store_.threads().erase(this);
}

void Thread::Mark() {
  for (auto&& frame : frames_) {
    frame.Mark(store_);
  }
  for (auto index : refs_) {
    store_.Mark(values_[index].Get<Ref>());
  }
  store_.Mark(exceptions_);
}

void Thread::PushValues(const ValueTypes& types, const Values& values) {
  assert(types.size() == values.size());
  for (size_t i = 0; i < types.size(); ++i) {
    if (IsReference(types[i])) {
      refs_.push_back(values_.size());
    }
    values_.push_back(values[i]);
  }
}

#define TRAP(msg) *out_trap = Trap::New(store_, (msg), frames_), RunResult::Trap
#define TRAP_IF(cond, msg)     \
  if (WABT_UNLIKELY((cond))) { \
    return TRAP(msg);          \
  }
#define TRAP_UNLESS(cond, msg) TRAP_IF(!(cond), msg)

Instance* Thread::GetCallerInstance() {
  if (frames_.size() < 2)
    return nullptr;
  return frames_[frames_.size() - 2].inst;
}

RunResult Thread::PushCall(Ref func, u32 offset, Trap::Ptr* out_trap) {
  TRAP_IF(frames_.size() == frames_.capacity(), "call stack exhausted");
  frames_.emplace_back(func, values_.size(), exceptions_.size(), offset, inst_,
                       mod_);
  return RunResult::Ok;
}

RunResult Thread::PushCall(const DefinedFunc& func, Trap::Ptr* out_trap) {
  TRAP_IF(frames_.size() == frames_.capacity(), "call stack exhausted");
  inst_ = store_.UnsafeGet<Instance>(func.instance()).get();
  mod_ = store_.UnsafeGet<Module>(inst_->module()).get();
  frames_.emplace_back(func.self(), values_.size(), exceptions_.size(),
                       func.desc().code_offset, inst_, mod_);
  return RunResult::Ok;
}

RunResult Thread::PushCall(const HostFunc& func, Trap::Ptr* out_trap) {
  TRAP_IF(frames_.size() == frames_.capacity(), "call stack exhausted");
  inst_ = nullptr;
  mod_ = nullptr;
  frames_.emplace_back(func.self(), values_.size(), exceptions_.size(), 0,
                       inst_, mod_);
  return RunResult::Ok;
}

RunResult Thread::PopCall() {
  // Sanity check that the exception stack was popped correctly.
  assert(frames_.back().exceptions == exceptions_.size());

  frames_.pop_back();
  if (frames_.empty()) {
    return RunResult::Return;
  }

  auto& frame = frames_.back();
  if (!frame.inst) {
    // Returning to a HostFunc called on this thread.
    return RunResult::Return;
  }

  inst_ = frame.inst;
  mod_ = frame.mod;
  return RunResult::Ok;
}

RunResult Thread::DoReturnCall(const Func::Ptr& func, Trap::Ptr* out_trap) {
  PopCall();
  DoCall(func, out_trap);
  return frames_.empty() ? RunResult::Return : RunResult::Ok;
}

void Thread::PopValues(const ValueTypes& types, Values* out_values) {
  assert(values_.size() >= types.size());
  out_values->resize(types.size());
  std::copy(values_.end() - types.size(), values_.end(), out_values->begin());
  values_.resize(values_.size() - types.size());
}

RunResult Thread::Run(Trap::Ptr* out_trap) {
  const int kDefaultInstructionCount = 1000;
  RunResult result;
  do {
    result = Run(kDefaultInstructionCount, out_trap);
  } while (result == RunResult::Ok);
  return result;
}

Value& Thread::Pick(Index index) {
  assert(index > 0 && index <= values_.size());
  return values_[values_.size() - index];
}

template <typename T>
T WABT_VECTORCALL Thread::Pop() {
  return Pop().Get<T>();
}

Value Thread::Pop() {
  if (!refs_.empty() && refs_.back() >= values_.size()) {
    refs_.pop_back();
  }
  auto value = values_.back();
  values_.pop_back();
  return value;
}

u64 Thread::PopPtr(const Memory::Ptr& memory) {
  return memory->type().limits.is_64 ? Pop<u64>() : Pop<u32>();
}

template <typename T>
void WABT_VECTORCALL Thread::Push(T value) {
  Push(Value::Make(value));
}

template <>
void Thread::Push<bool>(bool value) {
  Push(Value::Make(static_cast<u32>(value ? 1 : 0)));
}

void Thread::Push(Value value) {
  values_.push_back(value);
}

void Thread::Push(Ref ref) {
  refs_.push_back(values_.size());
  values_.push_back(Value::Make(ref));
}

#define RETURN_IF(code)                        \
  {                                            \
    RunResult res = code;                      \
    if (WABT_UNLIKELY(res != RunResult::Ok)) { \
      return res;                              \
    }                                          \
    break;                                     \
  }

RunResult Thread::Run(int num_instructions, Trap::Ptr* out_trap) {
  using O = Opcode;

  DefinedFunc::Ptr func{store_, frames_.back().func};
  for (; num_instructions > 0; --num_instructions) {
    u32& pc = frames_.back().offset;
    auto& istream = mod_->desc().istream;

    if (trace_stream_) {
      istream.Trace(trace_stream_, pc, trace_source_.get());
    }

    auto instr = istream.Read(&pc);
    switch (instr.op) {
      case O::Unreachable:
        return TRAP("unreachable executed");

      case O::Br:
        pc = instr.imm_u32;
        break;

      case O::BrIf:
        if (Pop<u32>()) {
          pc = instr.imm_u32;
        }
        break;

      case O::BrTable: {
        auto key = Pop<u32>();
        if (key >= instr.imm_u32) {
          key = instr.imm_u32;
        }
        pc += key * Istream::kBrTableEntrySize;
        break;
      }

      case O::Return:
        RETURN_IF((PopCall()));

      case O::Call: {
        Ref new_func_ref = inst_->funcs()[instr.imm_u32];
        DefinedFunc::Ptr new_func{store_, new_func_ref};
        if (PushCall(new_func_ref, new_func->desc().code_offset, out_trap) ==
            RunResult::Trap) {
          return RunResult::Trap;
        }
        break;
      }

      case O::CallIndirect:
      case O::ReturnCallIndirect: {
        Table::Ptr table{store_, inst_->tables()[instr.imm_u32x2.fst]};
        auto&& func_type = mod_->desc().func_types[instr.imm_u32x2.snd];
        auto entry = Pop<u32>();
        TRAP_IF(entry >= table->elements().size(), "undefined table index");
        auto new_func_ref = table->elements()[entry];
        TRAP_IF(new_func_ref == Ref::Null, "uninitialized table element");
        Func::Ptr new_func{store_, new_func_ref};
        TRAP_IF(
            Failed(Match(new_func->type(), func_type, nullptr)),
            "indirect call signature mismatch");  // TODO: don't use "signature"
        if (instr.op == O::ReturnCallIndirect) {
          RETURN_IF((DoReturnCall(new_func, out_trap)));
        } else {
          RETURN_IF((DoCall(new_func, out_trap)));
        }
      }

      case O::Drop:
        Pop();
        break;

      case O::Select: {
        // TODO: need to mark whether this is a ref.
        auto cond = Pop<u32>();
        Value false_ = Pop();
        Value true_ = Pop();
        Push(cond ? true_ : false_);
        break;
      }

      case O::LocalGet:
        // TODO: need to mark whether this is a ref.
        Push(Pick(instr.imm_u32));
        break;

      case O::LocalSet: {
        Pick(instr.imm_u32) = Pick(1);
        Pop();
        break;
      }

      case O::LocalTee:
        Pick(instr.imm_u32) = Pick(1);
        break;

      case O::GlobalGet: {
        // TODO: need to mark whether this is a ref.
        Global::Ptr global{store_, inst_->globals()[instr.imm_u32]};
        Push(global->Get());
        break;
      }

      case O::GlobalSet: {
        Global::Ptr global{store_, inst_->globals()[instr.imm_u32]};
        global->UnsafeSet(Pop());
        break;
      }

      case O::I32Load:
        RETURN_IF((DoLoad<u32>(instr, out_trap)));
      case O::I64Load:
        RETURN_IF((DoLoad<u64>(instr, out_trap)));
      case O::F32Load:
        RETURN_IF((DoLoad<f32>(instr, out_trap)));
      case O::F64Load:
        RETURN_IF((DoLoad<f64>(instr, out_trap)));
      case O::I32Load8S:
        RETURN_IF((DoLoad<s32, s8>(instr, out_trap)));
      case O::I32Load8U:
        RETURN_IF((DoLoad<u32, u8>(instr, out_trap)));
      case O::I32Load16S:
        RETURN_IF((DoLoad<s32, s16>(instr, out_trap)));
      case O::I32Load16U:
        RETURN_IF((DoLoad<u32, u16>(instr, out_trap)));
      case O::I64Load8S:
        RETURN_IF((DoLoad<s64, s8>(instr, out_trap)));
      case O::I64Load8U:
        RETURN_IF((DoLoad<u64, u8>(instr, out_trap)));
      case O::I64Load16S:
        RETURN_IF((DoLoad<s64, s16>(instr, out_trap)));
      case O::I64Load16U:
        RETURN_IF((DoLoad<u64, u16>(instr, out_trap)));
      case O::I64Load32S:
        RETURN_IF((DoLoad<s64, s32>(instr, out_trap)));
      case O::I64Load32U:
        RETURN_IF((DoLoad<u64, u32>(instr, out_trap)));

      case O::I32Store:
        RETURN_IF((DoStore<u32>(instr, out_trap)));
      case O::I64Store:
        RETURN_IF((DoStore<u64>(instr, out_trap)));
      case O::F32Store:
        RETURN_IF((DoStore<f32>(instr, out_trap)));
      case O::F64Store:
        RETURN_IF((DoStore<f64>(instr, out_trap)));
      case O::I32Store8:
        RETURN_IF((DoStore<u32, u8>(instr, out_trap)));
      case O::I32Store16:
        RETURN_IF((DoStore<u32, u16>(instr, out_trap)));
      case O::I64Store8:
        RETURN_IF((DoStore<u64, u8>(instr, out_trap)));
      case O::I64Store16:
        RETURN_IF((DoStore<u64, u16>(instr, out_trap)));
      case O::I64Store32:
        RETURN_IF((DoStore<u64, u32>(instr, out_trap)));

      case O::MemorySize: {
        Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32]};
        if (memory->type().limits.is_64) {
          Push<u64>(memory->PageSize());
        } else {
          Push<u32>(static_cast<u32>(memory->PageSize()));
        }
        break;
      }

      case O::MemoryGrow: {
        Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32]};
        u64 old_size = memory->PageSize();
        if (memory->type().limits.is_64) {
          if (Failed(memory->Grow(Pop<u64>()))) {
            Push<s64>(-1);
          } else {
            Push<u64>(old_size);
          }
        } else {
          if (Failed(memory->Grow(Pop<u32>()))) {
            Push<s32>(-1);
          } else {
            Push<u32>(old_size);
          }
        }
        break;
      }

      case O::I32Const:
        Push(instr.imm_u32);
        break;
      case O::F32Const:
        Push(instr.imm_f32);
        break;
      case O::I64Const:
        Push(instr.imm_u64);
        break;
      case O::F64Const:
        Push(instr.imm_f64);
        break;

      case O::I32Eqz:
        RETURN_IF((DoUnop(IntEqz<u32>)));
      case O::I32Eq:
        RETURN_IF((DoBinop(Eq<u32>)));
      case O::I32Ne:
        RETURN_IF((DoBinop(Ne<u32>)));
      case O::I32LtS:
        RETURN_IF((DoBinop(Lt<s32>)));
      case O::I32LtU:
        RETURN_IF((DoBinop(Lt<u32>)));
      case O::I32GtS:
        RETURN_IF((DoBinop(Gt<s32>)));
      case O::I32GtU:
        RETURN_IF((DoBinop(Gt<u32>)));
      case O::I32LeS:
        RETURN_IF((DoBinop(Le<s32>)));
      case O::I32LeU:
        RETURN_IF((DoBinop(Le<u32>)));
      case O::I32GeS:
        RETURN_IF((DoBinop(Ge<s32>)));
      case O::I32GeU:
        RETURN_IF((DoBinop(Ge<u32>)));

      case O::I64Eqz:
        RETURN_IF((DoUnop(IntEqz<u64>)));
      case O::I64Eq:
        RETURN_IF((DoBinop(Eq<u64>)));
      case O::I64Ne:
        RETURN_IF((DoBinop(Ne<u64>)));
      case O::I64LtS:
        RETURN_IF((DoBinop(Lt<s64>)));
      case O::I64LtU:
        RETURN_IF((DoBinop(Lt<u64>)));
      case O::I64GtS:
        RETURN_IF((DoBinop(Gt<s64>)));
      case O::I64GtU:
        RETURN_IF((DoBinop(Gt<u64>)));
      case O::I64LeS:
        RETURN_IF((DoBinop(Le<s64>)));
      case O::I64LeU:
        RETURN_IF((DoBinop(Le<u64>)));
      case O::I64GeS:
        RETURN_IF((DoBinop(Ge<s64>)));
      case O::I64GeU:
        RETURN_IF((DoBinop(Ge<u64>)));

      case O::F32Eq:
        RETURN_IF((DoBinop(Eq<f32>)));
      case O::F32Ne:
        RETURN_IF((DoBinop(Ne<f32>)));
      case O::F32Lt:
        RETURN_IF((DoBinop(Lt<f32>)));
      case O::F32Gt:
        RETURN_IF((DoBinop(Gt<f32>)));
      case O::F32Le:
        RETURN_IF((DoBinop(Le<f32>)));
      case O::F32Ge:
        RETURN_IF((DoBinop(Ge<f32>)));

      case O::F64Eq:
        RETURN_IF((DoBinop(Eq<f64>)));
      case O::F64Ne:
        RETURN_IF((DoBinop(Ne<f64>)));
      case O::F64Lt:
        RETURN_IF((DoBinop(Lt<f64>)));
      case O::F64Gt:
        RETURN_IF((DoBinop(Gt<f64>)));
      case O::F64Le:
        RETURN_IF((DoBinop(Le<f64>)));
      case O::F64Ge:
        RETURN_IF((DoBinop(Ge<f64>)));

      case O::I32Clz:
        RETURN_IF((DoUnop(IntClz<u32>)));
      case O::I32Ctz:
        RETURN_IF((DoUnop(IntCtz<u32>)));
      case O::I32Popcnt:
        RETURN_IF((DoUnop(IntPopcnt<u32>)));
      case O::I32Add:
        RETURN_IF((DoBinop(Add<u32>)));
      case O::I32Sub:
        RETURN_IF((DoBinop(Sub<u32>)));
      case O::I32Mul:
        RETURN_IF((DoBinop(Mul<u32>)));
      case O::I32DivS:
        RETURN_IF((DoBinop(IntDiv<s32>, out_trap)));
      case O::I32DivU:
        RETURN_IF((DoBinop(IntDiv<u32>, out_trap)));
      case O::I32RemS:
        RETURN_IF((DoBinop(IntRem<s32>, out_trap)));
      case O::I32RemU:
        RETURN_IF((DoBinop(IntRem<u32>, out_trap)));
      case O::I32And:
        RETURN_IF((DoBinop(IntAnd<u32>)));
      case O::I32Or:
        RETURN_IF((DoBinop(IntOr<u32>)));
      case O::I32Xor:
        RETURN_IF((DoBinop(IntXor<u32>)));
      case O::I32Shl:
        RETURN_IF((DoBinop(IntShl<u32>)));
      case O::I32ShrS:
        RETURN_IF((DoBinop(IntShr<s32>)));
      case O::I32ShrU:
        RETURN_IF((DoBinop(IntShr<u32>)));
      case O::I32Rotl:
        RETURN_IF((DoBinop(IntRotl<u32>)));
      case O::I32Rotr:
        RETURN_IF((DoBinop(IntRotr<u32>)));

      case O::I64Clz:
        RETURN_IF((DoUnop(IntClz<u64>)));
      case O::I64Ctz:
        RETURN_IF((DoUnop(IntCtz<u64>)));
      case O::I64Popcnt:
        RETURN_IF((DoUnop(IntPopcnt<u64>)));
      case O::I64Add:
        RETURN_IF((DoBinop(Add<u64>)));
      case O::I64Sub:
        RETURN_IF((DoBinop(Sub<u64>)));
      case O::I64Mul:
        RETURN_IF((DoBinop(Mul<u64>)));
      case O::I64DivS:
        RETURN_IF((DoBinop(IntDiv<s64>, out_trap)));
      case O::I64DivU:
        RETURN_IF((DoBinop(IntDiv<u64>, out_trap)));
      case O::I64RemS:
        RETURN_IF((DoBinop(IntRem<s64>, out_trap)));
      case O::I64RemU:
        RETURN_IF((DoBinop(IntRem<u64>, out_trap)));
      case O::I64And:
        RETURN_IF((DoBinop(IntAnd<u64>)));
      case O::I64Or:
        RETURN_IF((DoBinop(IntOr<u64>)));
      case O::I64Xor:
        RETURN_IF((DoBinop(IntXor<u64>)));
      case O::I64Shl:
        RETURN_IF((DoBinop(IntShl<u64>)));
      case O::I64ShrS:
        RETURN_IF((DoBinop(IntShr<s64>)));
      case O::I64ShrU:
        RETURN_IF((DoBinop(IntShr<u64>)));
      case O::I64Rotl:
        RETURN_IF((DoBinop(IntRotl<u64>)));
      case O::I64Rotr:
        RETURN_IF((DoBinop(IntRotr<u64>)));

      case O::F32Abs:
        RETURN_IF((DoUnop(FloatAbs<f32>)));
      case O::F32Neg:
        RETURN_IF((DoUnop(FloatNeg<f32>)));
      case O::F32Ceil:
        RETURN_IF((DoUnop(FloatCeil<f32>)));
      case O::F32Floor:
        RETURN_IF((DoUnop(FloatFloor<f32>)));
      case O::F32Trunc:
        RETURN_IF((DoUnop(FloatTrunc<f32>)));
      case O::F32Nearest:
        RETURN_IF((DoUnop(FloatNearest<f32>)));
      case O::F32Sqrt:
        RETURN_IF((DoUnop(FloatSqrt<f32>)));
      case O::F32Add:
        RETURN_IF((DoBinop(Add<f32>)));
      case O::F32Sub:
        RETURN_IF((DoBinop(Sub<f32>)));
      case O::F32Mul:
        RETURN_IF((DoBinop(Mul<f32>)));
      case O::F32Div:
        RETURN_IF((DoBinop(FloatDiv<f32>)));
      case O::F32Min:
        RETURN_IF((DoBinop(FloatMin<f32>)));
      case O::F32Max:
        RETURN_IF((DoBinop(FloatMax<f32>)));
      case O::F32Copysign:
        RETURN_IF((DoBinop(FloatCopysign<f32>)));

      case O::F64Abs:
        RETURN_IF((DoUnop(FloatAbs<f64>)));
      case O::F64Neg:
        RETURN_IF((DoUnop(FloatNeg<f64>)));
      case O::F64Ceil:
        RETURN_IF((DoUnop(FloatCeil<f64>)));
      case O::F64Floor:
        RETURN_IF((DoUnop(FloatFloor<f64>)));
      case O::F64Trunc:
        RETURN_IF((DoUnop(FloatTrunc<f64>)));
      case O::F64Nearest:
        RETURN_IF((DoUnop(FloatNearest<f64>)));
      case O::F64Sqrt:
        RETURN_IF((DoUnop(FloatSqrt<f64>)));
      case O::F64Add:
        RETURN_IF((DoBinop(Add<f64>)));
      case O::F64Sub:
        RETURN_IF((DoBinop(Sub<f64>)));
      case O::F64Mul:
        RETURN_IF((DoBinop(Mul<f64>)));
      case O::F64Div:
        RETURN_IF((DoBinop(FloatDiv<f64>)));
      case O::F64Min:
        RETURN_IF((DoBinop(FloatMin<f64>)));
      case O::F64Max:
        RETURN_IF((DoBinop(FloatMax<f64>)));
      case O::F64Copysign:
        RETURN_IF((DoBinop(FloatCopysign<f64>)));

      case O::I32WrapI64:
        RETURN_IF((DoConvert<u32, u64>(out_trap)));
      case O::I32TruncF32S:
        RETURN_IF((DoConvert<s32, f32>(out_trap)));
      case O::I32TruncF32U:
        RETURN_IF((DoConvert<u32, f32>(out_trap)));
      case O::I32TruncF64S:
        RETURN_IF((DoConvert<s32, f64>(out_trap)));
      case O::I32TruncF64U:
        RETURN_IF((DoConvert<u32, f64>(out_trap)));
      case O::I64ExtendI32S:
        RETURN_IF((DoConvert<s64, s32>(out_trap)));
      case O::I64ExtendI32U:
        RETURN_IF((DoConvert<u64, u32>(out_trap)));
      case O::I64TruncF32S:
        RETURN_IF((DoConvert<s64, f32>(out_trap)));
      case O::I64TruncF32U:
        RETURN_IF((DoConvert<u64, f32>(out_trap)));
      case O::I64TruncF64S:
        RETURN_IF((DoConvert<s64, f64>(out_trap)));
      case O::I64TruncF64U:
        RETURN_IF((DoConvert<u64, f64>(out_trap)));
      case O::F32ConvertI32S:
        RETURN_IF((DoConvert<f32, s32>(out_trap)));
      case O::F32ConvertI32U:
        RETURN_IF((DoConvert<f32, u32>(out_trap)));
      case O::F32ConvertI64S:
        RETURN_IF((DoConvert<f32, s64>(out_trap)));
      case O::F32ConvertI64U:
        RETURN_IF((DoConvert<f32, u64>(out_trap)));
      case O::F32DemoteF64:
        RETURN_IF((DoConvert<f32, f64>(out_trap)));
      case O::F64ConvertI32S:
        RETURN_IF((DoConvert<f64, s32>(out_trap)));
      case O::F64ConvertI32U:
        RETURN_IF((DoConvert<f64, u32>(out_trap)));
      case O::F64ConvertI64S:
        RETURN_IF((DoConvert<f64, s64>(out_trap)));
      case O::F64ConvertI64U:
        RETURN_IF((DoConvert<f64, u64>(out_trap)));
      case O::F64PromoteF32:
        RETURN_IF((DoConvert<f64, f32>(out_trap)));

      case O::I32ReinterpretF32:
        RETURN_IF((DoReinterpret<u32, f32>()));
      case O::F32ReinterpretI32:
        RETURN_IF((DoReinterpret<f32, u32>()));
      case O::I64ReinterpretF64:
        RETURN_IF((DoReinterpret<u64, f64>()));
      case O::F64ReinterpretI64:
        RETURN_IF((DoReinterpret<f64, u64>()));

      case O::I32Extend8S:
        RETURN_IF((DoUnop(IntExtend<u32, 7>)));
      case O::I32Extend16S:
        RETURN_IF((DoUnop(IntExtend<u32, 15>)));
      case O::I64Extend8S:
        RETURN_IF((DoUnop(IntExtend<u64, 7>)));
      case O::I64Extend16S:
        RETURN_IF((DoUnop(IntExtend<u64, 15>)));
      case O::I64Extend32S:
        RETURN_IF((DoUnop(IntExtend<u64, 31>)));

      case O::InterpAlloca:
        values_.resize(values_.size() + instr.imm_u32);
        // refs_ doesn't need to be updated; We may be allocating space for
        // references, but they will be initialized to null, so it is OK if we
        // don't mark them.
        break;

      case O::InterpBrUnless:
        if (!Pop<u32>()) {
          pc = instr.imm_u32;
        }
        break;

      case O::InterpCallImport: {
        Ref new_func_ref = inst_->funcs()[instr.imm_u32];
        Func::Ptr new_func{store_, new_func_ref};
        RETURN_IF((DoCall(new_func, out_trap)));
      }

      case O::InterpDropKeep: {
        auto drop = instr.imm_u32x2.fst;
        auto keep = instr.imm_u32x2.snd;
        // Shift kept refs down.
        for (auto iter = refs_.rbegin(); iter != refs_.rend(); ++iter) {
          if (*iter >= values_.size() - keep) {
            *iter -= drop;
          } else {
            break;
          }
        }
        std::move(values_.end() - keep, values_.end(),
                  values_.end() - drop - keep);
        values_.resize(values_.size() - drop);
        break;
      }

      case O::InterpCatchDrop: {
        auto drop = instr.imm_u32;
        for (u32 i = 0; i < drop; i++) {
          exceptions_.pop_back();
        }
        break;
      }

      // This operation adjusts the function reference of the reused frame
      // after a return_call. This ensures the correct exception handlers are
      // used for the call.
      case O::InterpAdjustFrameForReturnCall: {
        Ref new_func_ref = inst_->funcs()[instr.imm_u32];
        Frame& current_frame = frames_.back();
        current_frame.func = new_func_ref;
        break;
      }

      case O::I32TruncSatF32S:
        RETURN_IF((DoUnop(IntTruncSat<s32, f32>)));
      case O::I32TruncSatF32U:
        RETURN_IF((DoUnop(IntTruncSat<u32, f32>)));
      case O::I32TruncSatF64S:
        RETURN_IF((DoUnop(IntTruncSat<s32, f64>)));
      case O::I32TruncSatF64U:
        RETURN_IF((DoUnop(IntTruncSat<u32, f64>)));
      case O::I64TruncSatF32S:
        RETURN_IF((DoUnop(IntTruncSat<s64, f32>)));
      case O::I64TruncSatF32U:
        RETURN_IF((DoUnop(IntTruncSat<u64, f32>)));
      case O::I64TruncSatF64S:
        RETURN_IF((DoUnop(IntTruncSat<s64, f64>)));
      case O::I64TruncSatF64U:
        RETURN_IF((DoUnop(IntTruncSat<u64, f64>)));

      case O::MemoryInit:
        RETURN_IF((DoMemoryInit(instr, out_trap)));
      case O::DataDrop:
        RETURN_IF((DoDataDrop(instr)));
      case O::MemoryCopy:
        RETURN_IF((DoMemoryCopy(instr, out_trap)));
      case O::MemoryFill:
        RETURN_IF((DoMemoryFill(instr, out_trap)));

      case O::TableInit:
        RETURN_IF((DoTableInit(instr, out_trap)));
      case O::ElemDrop:
        RETURN_IF((DoElemDrop(instr)));
      case O::TableCopy:
        RETURN_IF((DoTableCopy(instr, out_trap)));
      case O::TableGet:
        RETURN_IF((DoTableGet(instr, out_trap)));
      case O::TableSet:
        RETURN_IF((DoTableSet(instr, out_trap)));
      case O::TableGrow:
        RETURN_IF((DoTableGrow(instr, out_trap)));
      case O::TableSize:
        RETURN_IF((DoTableSize(instr)));
      case O::TableFill:
        RETURN_IF((DoTableFill(instr, out_trap)));

      case O::RefNull:
        Push(Ref::Null);
        break;

      case O::RefIsNull:
        Push(Pop<Ref>() == Ref::Null);
        break;

      case O::RefFunc:
        Push(inst_->funcs()[instr.imm_u32]);
        break;

      case O::V128Load:
        RETURN_IF((DoLoad<v128>(instr, out_trap)));
      case O::V128Store:
        RETURN_IF((DoStore<v128>(instr, out_trap)));

      case O::V128Const:
        Push<v128>(instr.imm_v128);
        break;

      case O::I8X16Splat:
        RETURN_IF((DoSimdSplat<u8x16, u32>()));
      case O::I8X16ExtractLaneS:
        RETURN_IF((DoSimdExtract<s8x16, s32>(instr)));
      case O::I8X16ExtractLaneU:
        RETURN_IF((DoSimdExtract<u8x16, u32>(instr)));
      case O::I8X16ReplaceLane:
        RETURN_IF((DoSimdReplace<u8x16, u32>(instr)));
      case O::I16X8Splat:
        RETURN_IF((DoSimdSplat<u16x8, u32>()));
      case O::I16X8ExtractLaneS:
        RETURN_IF((DoSimdExtract<s16x8, s32>(instr)));
      case O::I16X8ExtractLaneU:
        RETURN_IF((DoSimdExtract<u16x8, u32>(instr)));
      case O::I16X8ReplaceLane:
        RETURN_IF((DoSimdReplace<u16x8, u32>(instr)));
      case O::I32X4Splat:
        RETURN_IF((DoSimdSplat<u32x4, u32>()));
      case O::I32X4ExtractLane:
        RETURN_IF((DoSimdExtract<s32x4, u32>(instr)));
      case O::I32X4ReplaceLane:
        RETURN_IF((DoSimdReplace<u32x4, u32>(instr)));
      case O::I64X2Splat:
        RETURN_IF((DoSimdSplat<u64x2, u64>()));
      case O::I64X2ExtractLane:
        RETURN_IF((DoSimdExtract<u64x2, u64>(instr)));
      case O::I64X2ReplaceLane:
        RETURN_IF((DoSimdReplace<u64x2, u64>(instr)));
      case O::F32X4Splat:
        RETURN_IF((DoSimdSplat<f32x4, f32>()));
      case O::F32X4ExtractLane:
        RETURN_IF((DoSimdExtract<f32x4, f32>(instr)));
      case O::F32X4ReplaceLane:
        RETURN_IF((DoSimdReplace<f32x4, f32>(instr)));
      case O::F64X2Splat:
        RETURN_IF((DoSimdSplat<f64x2, f64>()));
      case O::F64X2ExtractLane:
        RETURN_IF((DoSimdExtract<f64x2, f64>(instr)));
      case O::F64X2ReplaceLane:
        RETURN_IF((DoSimdReplace<f64x2, f64>(instr)));

      case O::I8X16Eq:
        RETURN_IF((DoSimdBinop(EqMask<u8>)));
      case O::I8X16Ne:
        RETURN_IF((DoSimdBinop(NeMask<u8>)));
      case O::I8X16LtS:
        RETURN_IF((DoSimdBinop(LtMask<s8>)));
      case O::I8X16LtU:
        RETURN_IF((DoSimdBinop(LtMask<u8>)));
      case O::I8X16GtS:
        RETURN_IF((DoSimdBinop(GtMask<s8>)));
      case O::I8X16GtU:
        RETURN_IF((DoSimdBinop(GtMask<u8>)));
      case O::I8X16LeS:
        RETURN_IF((DoSimdBinop(LeMask<s8>)));
      case O::I8X16LeU:
        RETURN_IF((DoSimdBinop(LeMask<u8>)));
      case O::I8X16GeS:
        RETURN_IF((DoSimdBinop(GeMask<s8>)));
      case O::I8X16GeU:
        RETURN_IF((DoSimdBinop(GeMask<u8>)));
      case O::I16X8Eq:
        RETURN_IF((DoSimdBinop(EqMask<u16>)));
      case O::I16X8Ne:
        RETURN_IF((DoSimdBinop(NeMask<u16>)));
      case O::I16X8LtS:
        RETURN_IF((DoSimdBinop(LtMask<s16>)));
      case O::I16X8LtU:
        RETURN_IF((DoSimdBinop(LtMask<u16>)));
      case O::I16X8GtS:
        RETURN_IF((DoSimdBinop(GtMask<s16>)));
      case O::I16X8GtU:
        RETURN_IF((DoSimdBinop(GtMask<u16>)));
      case O::I16X8LeS:
        RETURN_IF((DoSimdBinop(LeMask<s16>)));
      case O::I16X8LeU:
        RETURN_IF((DoSimdBinop(LeMask<u16>)));
      case O::I16X8GeS:
        RETURN_IF((DoSimdBinop(GeMask<s16>)));
      case O::I16X8GeU:
        RETURN_IF((DoSimdBinop(GeMask<u16>)));
      case O::I32X4Eq:
        RETURN_IF((DoSimdBinop(EqMask<u32>)));
      case O::I32X4Ne:
        RETURN_IF((DoSimdBinop(NeMask<u32>)));
      case O::I32X4LtS:
        RETURN_IF((DoSimdBinop(LtMask<s32>)));
      case O::I32X4LtU:
        RETURN_IF((DoSimdBinop(LtMask<u32>)));
      case O::I32X4GtS:
        RETURN_IF((DoSimdBinop(GtMask<s32>)));
      case O::I32X4GtU:
        RETURN_IF((DoSimdBinop(GtMask<u32>)));
      case O::I32X4LeS:
        RETURN_IF((DoSimdBinop(LeMask<s32>)));
      case O::I32X4LeU:
        RETURN_IF((DoSimdBinop(LeMask<u32>)));
      case O::I32X4GeS:
        RETURN_IF((DoSimdBinop(GeMask<s32>)));
      case O::I32X4GeU:
        RETURN_IF((DoSimdBinop(GeMask<u32>)));
      case O::I64X2Eq:
        RETURN_IF((DoSimdBinop(EqMask<u64>)));
      case O::I64X2Ne:
        RETURN_IF((DoSimdBinop(NeMask<u64>)));
      case O::I64X2LtS:
        RETURN_IF((DoSimdBinop(LtMask<s64>)));
      case O::I64X2GtS:
        RETURN_IF((DoSimdBinop(GtMask<s64>)));
      case O::I64X2LeS:
        RETURN_IF((DoSimdBinop(LeMask<s64>)));
      case O::I64X2GeS:
        RETURN_IF((DoSimdBinop(GeMask<s64>)));
      case O::F32X4Eq:
        RETURN_IF((DoSimdBinop(EqMask<f32>)));
      case O::F32X4Ne:
        RETURN_IF((DoSimdBinop(NeMask<f32>)));
      case O::F32X4Lt:
        RETURN_IF((DoSimdBinop(LtMask<f32>)));
      case O::F32X4Gt:
        RETURN_IF((DoSimdBinop(GtMask<f32>)));
      case O::F32X4Le:
        RETURN_IF((DoSimdBinop(LeMask<f32>)));
      case O::F32X4Ge:
        RETURN_IF((DoSimdBinop(GeMask<f32>)));
      case O::F64X2Eq:
        RETURN_IF((DoSimdBinop(EqMask<f64>)));
      case O::F64X2Ne:
        RETURN_IF((DoSimdBinop(NeMask<f64>)));
      case O::F64X2Lt:
        RETURN_IF((DoSimdBinop(LtMask<f64>)));
      case O::F64X2Gt:
        RETURN_IF((DoSimdBinop(GtMask<f64>)));
      case O::F64X2Le:
        RETURN_IF((DoSimdBinop(LeMask<f64>)));
      case O::F64X2Ge:
        RETURN_IF((DoSimdBinop(GeMask<f64>)));

      case O::V128Not:
        RETURN_IF((DoSimdUnop(IntNot<u64>)));
      case O::V128And:
        RETURN_IF((DoSimdBinop(IntAnd<u64>)));
      case O::V128Or:
        RETURN_IF((DoSimdBinop(IntOr<u64>)));
      case O::V128Xor:
        RETURN_IF((DoSimdBinop(IntXor<u64>)));
      case O::V128BitSelect:
        RETURN_IF((DoSimdBitSelect()));
      case O::V128AnyTrue:
        RETURN_IF((DoSimdIsTrue<u8x16, 1>()));

      case O::I8X16Neg:
        RETURN_IF((DoSimdUnop(IntNeg<u8>)));
      case O::I8X16Bitmask:
        RETURN_IF((DoSimdBitmask<s8x16>()));
      case O::I8X16AllTrue:
        RETURN_IF((DoSimdIsTrue<u8x16, 16>()));
      case O::I8X16Shl:
        RETURN_IF((DoSimdShift(IntShl<u8>)));
      case O::I8X16ShrS:
        RETURN_IF((DoSimdShift(IntShr<s8>)));
      case O::I8X16ShrU:
        RETURN_IF((DoSimdShift(IntShr<u8>)));
      case O::I8X16Add:
        RETURN_IF((DoSimdBinop(Add<u8>)));
      case O::I8X16AddSatS:
        RETURN_IF((DoSimdBinop(IntAddSat<s8>)));
      case O::I8X16AddSatU:
        RETURN_IF((DoSimdBinop(IntAddSat<u8>)));
      case O::I8X16Sub:
        RETURN_IF((DoSimdBinop(Sub<u8>)));
      case O::I8X16SubSatS:
        RETURN_IF((DoSimdBinop(IntSubSat<s8>)));
      case O::I8X16SubSatU:
        RETURN_IF((DoSimdBinop(IntSubSat<u8>)));
      case O::I8X16MinS:
        RETURN_IF((DoSimdBinop(IntMin<s8>)));
      case O::I8X16MinU:
        RETURN_IF((DoSimdBinop(IntMin<u8>)));
      case O::I8X16MaxS:
        RETURN_IF((DoSimdBinop(IntMax<s8>)));
      case O::I8X16MaxU:
        RETURN_IF((DoSimdBinop(IntMax<u8>)));

      case O::I16X8Neg:
        RETURN_IF((DoSimdUnop(IntNeg<u16>)));
      case O::I16X8Bitmask:
        RETURN_IF((DoSimdBitmask<s16x8>()));
      case O::I16X8AllTrue:
        RETURN_IF((DoSimdIsTrue<u16x8, 8>()));
      case O::I16X8Shl:
        RETURN_IF((DoSimdShift(IntShl<u16>)));
      case O::I16X8ShrS:
        RETURN_IF((DoSimdShift(IntShr<s16>)));
      case O::I16X8ShrU:
        RETURN_IF((DoSimdShift(IntShr<u16>)));
      case O::I16X8Add:
        RETURN_IF((DoSimdBinop(Add<u16>)));
      case O::I16X8AddSatS:
        RETURN_IF((DoSimdBinop(IntAddSat<s16>)));
      case O::I16X8AddSatU:
        RETURN_IF((DoSimdBinop(IntAddSat<u16>)));
      case O::I16X8Sub:
        RETURN_IF((DoSimdBinop(Sub<u16>)));
      case O::I16X8SubSatS:
        RETURN_IF((DoSimdBinop(IntSubSat<s16>)));
      case O::I16X8SubSatU:
        RETURN_IF((DoSimdBinop(IntSubSat<u16>)));
      case O::I16X8Mul:
        RETURN_IF((DoSimdBinop(Mul<u16>)));
      case O::I16X8MinS:
        RETURN_IF((DoSimdBinop(IntMin<s16>)));
      case O::I16X8MinU:
        RETURN_IF((DoSimdBinop(IntMin<u16>)));
      case O::I16X8MaxS:
        RETURN_IF((DoSimdBinop(IntMax<s16>)));
      case O::I16X8MaxU:
        RETURN_IF((DoSimdBinop(IntMax<u16>)));

      case O::I32X4Neg:
        RETURN_IF((DoSimdUnop(IntNeg<u32>)));
      case O::I32X4Bitmask:
        RETURN_IF((DoSimdBitmask<s32x4>()));
      case O::I32X4AllTrue:
        RETURN_IF((DoSimdIsTrue<u32x4, 4>()));
      case O::I32X4Shl:
        RETURN_IF((DoSimdShift(IntShl<u32>)));
      case O::I32X4ShrS:
        RETURN_IF((DoSimdShift(IntShr<s32>)));
      case O::I32X4ShrU:
        RETURN_IF((DoSimdShift(IntShr<u32>)));
      case O::I32X4Add:
        RETURN_IF((DoSimdBinop(Add<u32>)));
      case O::I32X4Sub:
        RETURN_IF((DoSimdBinop(Sub<u32>)));
      case O::I32X4Mul:
        RETURN_IF((DoSimdBinop(Mul<u32>)));
      case O::I32X4MinS:
        RETURN_IF((DoSimdBinop(IntMin<s32>)));
      case O::I32X4MinU:
        RETURN_IF((DoSimdBinop(IntMin<u32>)));
      case O::I32X4MaxS:
        RETURN_IF((DoSimdBinop(IntMax<s32>)));
      case O::I32X4MaxU:
        RETURN_IF((DoSimdBinop(IntMax<u32>)));

      case O::I64X2Neg:
        RETURN_IF((DoSimdUnop(IntNeg<u64>)));
      case O::I64X2Bitmask:
        RETURN_IF((DoSimdBitmask<s64x2>()));
      case O::I64X2AllTrue:
        RETURN_IF((DoSimdIsTrue<u64x2, 2>()));
      case O::I64X2Shl:
        RETURN_IF((DoSimdShift(IntShl<u64>)));
      case O::I64X2ShrS:
        RETURN_IF((DoSimdShift(IntShr<s64>)));
      case O::I64X2ShrU:
        RETURN_IF((DoSimdShift(IntShr<u64>)));
      case O::I64X2Add:
        RETURN_IF((DoSimdBinop(Add<u64>)));
      case O::I64X2Sub:
        RETURN_IF((DoSimdBinop(Sub<u64>)));
      case O::I64X2Mul:
        RETURN_IF((DoSimdBinop(Mul<u64>)));

      case O::F32X4Ceil:
        RETURN_IF((DoSimdUnop(FloatCeil<f32>)));
      case O::F32X4Floor:
        RETURN_IF((DoSimdUnop(FloatFloor<f32>)));
      case O::F32X4Trunc:
        RETURN_IF((DoSimdUnop(FloatTrunc<f32>)));
      case O::F32X4Nearest:
        RETURN_IF((DoSimdUnop(FloatNearest<f32>)));

      case O::F64X2Ceil:
        RETURN_IF((DoSimdUnop(FloatCeil<f64>)));
      case O::F64X2Floor:
        RETURN_IF((DoSimdUnop(FloatFloor<f64>)));
      case O::F64X2Trunc:
        RETURN_IF((DoSimdUnop(FloatTrunc<f64>)));
      case O::F64X2Nearest:
        RETURN_IF((DoSimdUnop(FloatNearest<f64>)));

      case O::F32X4Abs:
        RETURN_IF((DoSimdUnop(FloatAbs<f32>)));
      case O::F32X4Neg:
        RETURN_IF((DoSimdUnop(FloatNeg<f32>)));
      case O::F32X4Sqrt:
        RETURN_IF((DoSimdUnop(FloatSqrt<f32>)));
      case O::F32X4Add:
        RETURN_IF((DoSimdBinop(Add<f32>)));
      case O::F32X4Sub:
        RETURN_IF((DoSimdBinop(Sub<f32>)));
      case O::F32X4Mul:
        RETURN_IF((DoSimdBinop(Mul<f32>)));
      case O::F32X4Div:
        RETURN_IF((DoSimdBinop(FloatDiv<f32>)));
      case O::F32X4Min:
        RETURN_IF((DoSimdBinop(FloatMin<f32>)));
      case O::F32X4Max:
        RETURN_IF((DoSimdBinop(FloatMax<f32>)));
      case O::F32X4PMin:
        RETURN_IF((DoSimdBinop(FloatPMin<f32>)));
      case O::F32X4PMax:
        RETURN_IF((DoSimdBinop(FloatPMax<f32>)));

      case O::F64X2Abs:
        RETURN_IF((DoSimdUnop(FloatAbs<f64>)));
      case O::F64X2Neg:
        RETURN_IF((DoSimdUnop(FloatNeg<f64>)));
      case O::F64X2Sqrt:
        RETURN_IF((DoSimdUnop(FloatSqrt<f64>)));
      case O::F64X2Add:
        RETURN_IF((DoSimdBinop(Add<f64>)));
      case O::F64X2Sub:
        RETURN_IF((DoSimdBinop(Sub<f64>)));
      case O::F64X2Mul:
        RETURN_IF((DoSimdBinop(Mul<f64>)));
      case O::F64X2Div:
        RETURN_IF((DoSimdBinop(FloatDiv<f64>)));
      case O::F64X2Min:
        RETURN_IF((DoSimdBinop(FloatMin<f64>)));
      case O::F64X2Max:
        RETURN_IF((DoSimdBinop(FloatMax<f64>)));
      case O::F64X2PMin:
        RETURN_IF((DoSimdBinop(FloatPMin<f64>)));
      case O::F64X2PMax:
        RETURN_IF((DoSimdBinop(FloatPMax<f64>)));

      case O::I32X4TruncSatF32X4S:
        RETURN_IF((DoSimdUnop(IntTruncSat<s32, f32>)));
      case O::I32X4TruncSatF32X4U:
        RETURN_IF((DoSimdUnop(IntTruncSat<u32, f32>)));
      case O::F32X4ConvertI32X4S:
        RETURN_IF((DoSimdUnop(Convert<f32, s32>)));
      case O::F32X4ConvertI32X4U:
        RETURN_IF((DoSimdUnop(Convert<f32, u32>)));
      case O::F32X4DemoteF64X2Zero:
        RETURN_IF((DoSimdUnopZero(Convert<f32, f64>)));
      case O::F64X2PromoteLowF32X4:
        RETURN_IF((DoSimdConvert<f64x2, f32x4, true>()));
      case O::I32X4TruncSatF64X2SZero:
        RETURN_IF((DoSimdUnopZero(IntTruncSat<s32, f64>)));
      case O::I32X4TruncSatF64X2UZero:
        RETURN_IF((DoSimdUnopZero(IntTruncSat<u32, f64>)));
      case O::F64X2ConvertLowI32X4S:
        RETURN_IF((DoSimdConvert<f64x2, s32x4, true>()));
      case O::F64X2ConvertLowI32X4U:
        RETURN_IF((DoSimdConvert<f64x2, u32x4, true>()));

      case O::I8X16Swizzle:
        RETURN_IF((DoSimdSwizzle()));
      case O::I8X16Shuffle:
        RETURN_IF((DoSimdShuffle(instr)));

      case O::V128Load8Splat:
        RETURN_IF((DoSimdLoadSplat<u8x16>(instr, out_trap)));
      case O::V128Load16Splat:
        RETURN_IF((DoSimdLoadSplat<u16x8>(instr, out_trap)));
      case O::V128Load32Splat:
        RETURN_IF((DoSimdLoadSplat<u32x4>(instr, out_trap)));
      case O::V128Load64Splat:
        RETURN_IF((DoSimdLoadSplat<u64x2>(instr, out_trap)));

      case O::V128Load8Lane:
        RETURN_IF((DoSimdLoadLane<u8x16>(instr, out_trap)));
      case O::V128Load16Lane:
        RETURN_IF((DoSimdLoadLane<u16x8>(instr, out_trap)));
      case O::V128Load32Lane:
        RETURN_IF((DoSimdLoadLane<u32x4>(instr, out_trap)));
      case O::V128Load64Lane:
        RETURN_IF((DoSimdLoadLane<u64x2>(instr, out_trap)));

      case O::V128Store8Lane:
        RETURN_IF((DoSimdStoreLane<u8x16>(instr, out_trap)));
      case O::V128Store16Lane:
        RETURN_IF((DoSimdStoreLane<u16x8>(instr, out_trap)));
      case O::V128Store32Lane:
        RETURN_IF((DoSimdStoreLane<u32x4>(instr, out_trap)));
      case O::V128Store64Lane:
        RETURN_IF((DoSimdStoreLane<u64x2>(instr, out_trap)));

      case O::V128Load32Zero:
        RETURN_IF((DoSimdLoadZero<u32x4, u32>(instr, out_trap)));
      case O::V128Load64Zero:
        RETURN_IF((DoSimdLoadZero<u64x2, u64>(instr, out_trap)));

      case O::I8X16NarrowI16X8S:
        RETURN_IF((DoSimdNarrow<s8x16, s16x8>()));
      case O::I8X16NarrowI16X8U:
        RETURN_IF((DoSimdNarrow<u8x16, s16x8>()));
      case O::I16X8NarrowI32X4S:
        RETURN_IF((DoSimdNarrow<s16x8, s32x4>()));
      case O::I16X8NarrowI32X4U:
        RETURN_IF((DoSimdNarrow<u16x8, s32x4>()));
      case O::I16X8ExtendLowI8X16S:
        RETURN_IF((DoSimdConvert<s16x8, s8x16, true>()));
      case O::I16X8ExtendHighI8X16S:
        RETURN_IF((DoSimdConvert<s16x8, s8x16, false>()));
      case O::I16X8ExtendLowI8X16U:
        RETURN_IF((DoSimdConvert<u16x8, u8x16, true>()));
      case O::I16X8ExtendHighI8X16U:
        RETURN_IF((DoSimdConvert<u16x8, u8x16, false>()));
      case O::I32X4ExtendLowI16X8S:
        RETURN_IF((DoSimdConvert<s32x4, s16x8, true>()));
      case O::I32X4ExtendHighI16X8S:
        RETURN_IF((DoSimdConvert<s32x4, s16x8, false>()));
      case O::I32X4ExtendLowI16X8U:
        RETURN_IF((DoSimdConvert<u32x4, u16x8, true>()));
      case O::I32X4ExtendHighI16X8U:
        RETURN_IF((DoSimdConvert<u32x4, u16x8, false>()));
      case O::I64X2ExtendLowI32X4S:
        RETURN_IF((DoSimdConvert<s64x2, s32x4, true>()));
      case O::I64X2ExtendHighI32X4S:
        RETURN_IF((DoSimdConvert<s64x2, s32x4, false>()));
      case O::I64X2ExtendLowI32X4U:
        RETURN_IF((DoSimdConvert<u64x2, u32x4, true>()));
      case O::I64X2ExtendHighI32X4U:
        RETURN_IF((DoSimdConvert<u64x2, u32x4, false>()));

      case O::V128Load8X8S:
        RETURN_IF((DoSimdLoadExtend<s16x8, s8x8>(instr, out_trap)));
      case O::V128Load8X8U:
        RETURN_IF((DoSimdLoadExtend<u16x8, u8x8>(instr, out_trap)));
      case O::V128Load16X4S:
        RETURN_IF((DoSimdLoadExtend<s32x4, s16x4>(instr, out_trap)));
      case O::V128Load16X4U:
        RETURN_IF((DoSimdLoadExtend<u32x4, u16x4>(instr, out_trap)));
      case O::V128Load32X2S:
        RETURN_IF((DoSimdLoadExtend<s64x2, s32x2>(instr, out_trap)));
      case O::V128Load32X2U:
        RETURN_IF((DoSimdLoadExtend<u64x2, u32x2>(instr, out_trap)));

      case O::V128Andnot:
        RETURN_IF((DoSimdBinop(IntAndNot<u64>)));
      case O::I8X16AvgrU:
        RETURN_IF((DoSimdBinop(IntAvgr<u8>)));
      case O::I16X8AvgrU:
        RETURN_IF((DoSimdBinop(IntAvgr<u16>)));

      case O::I8X16Abs:
        RETURN_IF((DoSimdUnop(IntAbs<u8>)));
      case O::I16X8Abs:
        RETURN_IF((DoSimdUnop(IntAbs<u16>)));
      case O::I32X4Abs:
        RETURN_IF((DoSimdUnop(IntAbs<u32>)));
      case O::I64X2Abs:
        RETURN_IF((DoSimdUnop(IntAbs<u64>)));

      case O::I8X16Popcnt:
        RETURN_IF((DoSimdUnop(IntPopcnt<u8>)));

      case O::I16X8ExtaddPairwiseI8X16S:
        RETURN_IF((DoSimdExtaddPairwise<s16x8, s8x16>()));
      case O::I16X8ExtaddPairwiseI8X16U:
        RETURN_IF((DoSimdExtaddPairwise<u16x8, u8x16>()));
      case O::I32X4ExtaddPairwiseI16X8S:
        RETURN_IF((DoSimdExtaddPairwise<s32x4, s16x8>()));
      case O::I32X4ExtaddPairwiseI16X8U:
        RETURN_IF((DoSimdExtaddPairwise<u32x4, u16x8>()));

      case O::I16X8ExtmulLowI8X16S:
        RETURN_IF((DoSimdExtmul<s16x8, s8x16, true>()));
      case O::I16X8ExtmulHighI8X16S:
        RETURN_IF((DoSimdExtmul<s16x8, s8x16, false>()));
      case O::I16X8ExtmulLowI8X16U:
        RETURN_IF((DoSimdExtmul<u16x8, u8x16, true>()));
      case O::I16X8ExtmulHighI8X16U:
        RETURN_IF((DoSimdExtmul<u16x8, u8x16, false>()));
      case O::I32X4ExtmulLowI16X8S:
        RETURN_IF((DoSimdExtmul<s32x4, s16x8, true>()));
      case O::I32X4ExtmulHighI16X8S:
        RETURN_IF((DoSimdExtmul<s32x4, s16x8, false>()));
      case O::I32X4ExtmulLowI16X8U:
        RETURN_IF((DoSimdExtmul<u32x4, u16x8, true>()));
      case O::I32X4ExtmulHighI16X8U:
        RETURN_IF((DoSimdExtmul<u32x4, u16x8, false>()));
      case O::I64X2ExtmulLowI32X4S:
        RETURN_IF((DoSimdExtmul<s64x2, s32x4, true>()));
      case O::I64X2ExtmulHighI32X4S:
        RETURN_IF((DoSimdExtmul<s64x2, s32x4, false>()));
      case O::I64X2ExtmulLowI32X4U:
        RETURN_IF((DoSimdExtmul<u64x2, u32x4, true>()));
      case O::I64X2ExtmulHighI32X4U:
        RETURN_IF((DoSimdExtmul<u64x2, u32x4, false>()));

      case O::I16X8Q15mulrSatS:
        RETURN_IF((DoSimdBinop(SaturatingRoundingQMul<s16>)));

      case O::I32X4DotI16X8S:
        RETURN_IF((DoSimdDot<u32x4, s16x8>()));

      case O::AtomicFence:
      case O::MemoryAtomicNotify:
      case O::MemoryAtomicWait32:
      case O::MemoryAtomicWait64:
        RETURN_IF((TRAP("not implemented")));

      case O::I32AtomicLoad:
        RETURN_IF((DoAtomicLoad<u32>(instr, out_trap)));
      case O::I64AtomicLoad:
        RETURN_IF((DoAtomicLoad<u64>(instr, out_trap)));
      case O::I32AtomicLoad8U:
        RETURN_IF((DoAtomicLoad<u32, u8>(instr, out_trap)));
      case O::I32AtomicLoad16U:
        RETURN_IF((DoAtomicLoad<u32, u16>(instr, out_trap)));
      case O::I64AtomicLoad8U:
        RETURN_IF((DoAtomicLoad<u64, u8>(instr, out_trap)));
      case O::I64AtomicLoad16U:
        RETURN_IF((DoAtomicLoad<u64, u16>(instr, out_trap)));
      case O::I64AtomicLoad32U:
        RETURN_IF((DoAtomicLoad<u64, u32>(instr, out_trap)));
      case O::I32AtomicStore:
        RETURN_IF((DoAtomicStore<u32>(instr, out_trap)));
      case O::I64AtomicStore:
        RETURN_IF((DoAtomicStore<u64>(instr, out_trap)));
      case O::I32AtomicStore8:
        RETURN_IF((DoAtomicStore<u32, u8>(instr, out_trap)));
      case O::I32AtomicStore16:
        RETURN_IF((DoAtomicStore<u32, u16>(instr, out_trap)));
      case O::I64AtomicStore8:
        RETURN_IF((DoAtomicStore<u64, u8>(instr, out_trap)));
      case O::I64AtomicStore16:
        RETURN_IF((DoAtomicStore<u64, u16>(instr, out_trap)));
      case O::I64AtomicStore32:
        RETURN_IF((DoAtomicStore<u64, u32>(instr, out_trap)));
      case O::I32AtomicRmwAdd:
        RETURN_IF((DoAtomicRmw<u32>(Add<u32>, instr, out_trap)));
      case O::I64AtomicRmwAdd:
        RETURN_IF((DoAtomicRmw<u64>(Add<u64>, instr, out_trap)));
      case O::I32AtomicRmw8AddU:
        RETURN_IF((DoAtomicRmw<u32>(Add<u8>, instr, out_trap)));
      case O::I32AtomicRmw16AddU:
        RETURN_IF((DoAtomicRmw<u32>(Add<u16>, instr, out_trap)));
      case O::I64AtomicRmw8AddU:
        RETURN_IF((DoAtomicRmw<u64>(Add<u8>, instr, out_trap)));
      case O::I64AtomicRmw16AddU:
        RETURN_IF((DoAtomicRmw<u64>(Add<u16>, instr, out_trap)));
      case O::I64AtomicRmw32AddU:
        RETURN_IF((DoAtomicRmw<u64>(Add<u32>, instr, out_trap)));
      case O::I32AtomicRmwSub:
        RETURN_IF((DoAtomicRmw<u32>(Sub<u32>, instr, out_trap)));
      case O::I64AtomicRmwSub:
        RETURN_IF((DoAtomicRmw<u64>(Sub<u64>, instr, out_trap)));
      case O::I32AtomicRmw8SubU:
        RETURN_IF((DoAtomicRmw<u32>(Sub<u8>, instr, out_trap)));
      case O::I32AtomicRmw16SubU:
        RETURN_IF((DoAtomicRmw<u32>(Sub<u16>, instr, out_trap)));
      case O::I64AtomicRmw8SubU:
        RETURN_IF((DoAtomicRmw<u64>(Sub<u8>, instr, out_trap)));
      case O::I64AtomicRmw16SubU:
        RETURN_IF((DoAtomicRmw<u64>(Sub<u16>, instr, out_trap)));
      case O::I64AtomicRmw32SubU:
        RETURN_IF((DoAtomicRmw<u64>(Sub<u32>, instr, out_trap)));
      case O::I32AtomicRmwAnd:
        RETURN_IF((DoAtomicRmw<u32>(IntAnd<u32>, instr, out_trap)));
      case O::I64AtomicRmwAnd:
        RETURN_IF((DoAtomicRmw<u64>(IntAnd<u64>, instr, out_trap)));
      case O::I32AtomicRmw8AndU:
        RETURN_IF((DoAtomicRmw<u32>(IntAnd<u8>, instr, out_trap)));
      case O::I32AtomicRmw16AndU:
        RETURN_IF((DoAtomicRmw<u32>(IntAnd<u16>, instr, out_trap)));
      case O::I64AtomicRmw8AndU:
        RETURN_IF((DoAtomicRmw<u64>(IntAnd<u8>, instr, out_trap)));
      case O::I64AtomicRmw16AndU:
        RETURN_IF((DoAtomicRmw<u64>(IntAnd<u16>, instr, out_trap)));
      case O::I64AtomicRmw32AndU:
        RETURN_IF((DoAtomicRmw<u64>(IntAnd<u32>, instr, out_trap)));
      case O::I32AtomicRmwOr:
        RETURN_IF((DoAtomicRmw<u32>(IntOr<u32>, instr, out_trap)));
      case O::I64AtomicRmwOr:
        RETURN_IF((DoAtomicRmw<u64>(IntOr<u64>, instr, out_trap)));
      case O::I32AtomicRmw8OrU:
        RETURN_IF((DoAtomicRmw<u32>(IntOr<u8>, instr, out_trap)));
      case O::I32AtomicRmw16OrU:
        RETURN_IF((DoAtomicRmw<u32>(IntOr<u16>, instr, out_trap)));
      case O::I64AtomicRmw8OrU:
        RETURN_IF((DoAtomicRmw<u64>(IntOr<u8>, instr, out_trap)));
      case O::I64AtomicRmw16OrU:
        RETURN_IF((DoAtomicRmw<u64>(IntOr<u16>, instr, out_trap)));
      case O::I64AtomicRmw32OrU:
        RETURN_IF((DoAtomicRmw<u64>(IntOr<u32>, instr, out_trap)));
      case O::I32AtomicRmwXor:
        RETURN_IF((DoAtomicRmw<u32>(IntXor<u32>, instr, out_trap)));
      case O::I64AtomicRmwXor:
        RETURN_IF((DoAtomicRmw<u64>(IntXor<u64>, instr, out_trap)));
      case O::I32AtomicRmw8XorU:
        RETURN_IF((DoAtomicRmw<u32>(IntXor<u8>, instr, out_trap)));
      case O::I32AtomicRmw16XorU:
        RETURN_IF((DoAtomicRmw<u32>(IntXor<u16>, instr, out_trap)));
      case O::I64AtomicRmw8XorU:
        RETURN_IF((DoAtomicRmw<u64>(IntXor<u8>, instr, out_trap)));
      case O::I64AtomicRmw16XorU:
        RETURN_IF((DoAtomicRmw<u64>(IntXor<u16>, instr, out_trap)));
      case O::I64AtomicRmw32XorU:
        RETURN_IF((DoAtomicRmw<u64>(IntXor<u32>, instr, out_trap)));
      case O::I32AtomicRmwXchg:
        RETURN_IF((DoAtomicRmw<u32>(Xchg<u32>, instr, out_trap)));
      case O::I64AtomicRmwXchg:
        RETURN_IF((DoAtomicRmw<u64>(Xchg<u64>, instr, out_trap)));
      case O::I32AtomicRmw8XchgU:
        RETURN_IF((DoAtomicRmw<u32>(Xchg<u8>, instr, out_trap)));
      case O::I32AtomicRmw16XchgU:
        RETURN_IF((DoAtomicRmw<u32>(Xchg<u16>, instr, out_trap)));
      case O::I64AtomicRmw8XchgU:
        RETURN_IF((DoAtomicRmw<u64>(Xchg<u8>, instr, out_trap)));
      case O::I64AtomicRmw16XchgU:
        RETURN_IF((DoAtomicRmw<u64>(Xchg<u16>, instr, out_trap)));
      case O::I64AtomicRmw32XchgU:
        RETURN_IF((DoAtomicRmw<u64>(Xchg<u32>, instr, out_trap)));

      case O::I32AtomicRmwCmpxchg:
        RETURN_IF((DoAtomicRmwCmpxchg<u32>(instr, out_trap)));
      case O::I64AtomicRmwCmpxchg:
        RETURN_IF((DoAtomicRmwCmpxchg<u64>(instr, out_trap)));
      case O::I32AtomicRmw8CmpxchgU:
        RETURN_IF((DoAtomicRmwCmpxchg<u32, u8>(instr, out_trap)));
      case O::I32AtomicRmw16CmpxchgU:
        RETURN_IF((DoAtomicRmwCmpxchg<u32, u16>(instr, out_trap)));
      case O::I64AtomicRmw8CmpxchgU:
        RETURN_IF((DoAtomicRmwCmpxchg<u64, u8>(instr, out_trap)));
      case O::I64AtomicRmw16CmpxchgU:
        RETURN_IF((DoAtomicRmwCmpxchg<u64, u16>(instr, out_trap)));
      case O::I64AtomicRmw32CmpxchgU:
        RETURN_IF((DoAtomicRmwCmpxchg<u64, u32>(instr, out_trap)));

      case O::Throw: {
        u32 tag_index = instr.imm_u32;
        Values params;
        Ref tag_ref = inst_->tags()[tag_index];
        Tag::Ptr tag{store_, tag_ref};
        PopValues(tag->type().signature, &params);
        Exception::Ptr exn = Exception::New(store_, tag_ref, params);
        RETURN_IF((DoThrow(exn)));
      }
      case O::Rethrow: {
        u32 exn_index = instr.imm_u32;
        Exception::Ptr exn{store_,
                           exceptions_[exceptions_.size() - exn_index - 1]};
        RETURN_IF((DoThrow(exn)));
      }

      // The following opcodes are either never generated or should never be
      // executed.
      case O::Nop:
      case O::Block:
      case O::Loop:
      case O::If:
      case O::Else:
      case O::End:
      case O::ReturnCall:
      case O::SelectT:

      case O::CallRef:
      case O::Try:
      case O::Catch:
      case O::CatchAll:
      case O::Delegate:
      case O::InterpData:
      case O::Invalid:
        WABT_UNREACHABLE;
        break;
    }
  }
  return RunResult::Ok;
}

RunResult Thread::DoCall(const Func::Ptr& func, Trap::Ptr* out_trap) {
  if (auto* host_func = dyn_cast<HostFunc>(func.get())) {
    auto& func_type = host_func->type();

    Values params;
    PopValues(func_type.params, &params);
    if (PushCall(*host_func, out_trap) == RunResult::Trap) {
      return RunResult::Trap;
    }

    Values results(func_type.results.size());
    if (Failed(host_func->Call(*this, params, results, out_trap))) {
      return RunResult::Trap;
    }

    PopCall();
    PushValues(func_type.results, results);
  } else {
    if (PushCall(*cast<DefinedFunc>(func.get()), out_trap) == RunResult::Trap) {
      return RunResult::Ok;
    }
  }
  return RunResult::Ok;
}

template <typename T>
RunResult Thread::Load(Instr instr, T* out, Trap::Ptr* out_trap) {
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32x2.fst]};
  u64 offset = PopPtr(memory);
  TRAP_IF(Failed(memory->Load(offset, instr.imm_u32x2.snd, out)),
          StringPrintf("out of bounds memory access: access at %" PRIu64
                       "+%" PRIzd " >= max value %" PRIu64,
                       offset + instr.imm_u32x2.snd, sizeof(T),
                       memory->ByteSize()));
  return RunResult::Ok;
}

template <typename T, typename V>
RunResult Thread::DoLoad(Instr instr, Trap::Ptr* out_trap) {
  V val;
  if (Load<V>(instr, &val, out_trap) != RunResult::Ok) {
    return RunResult::Trap;
  }
  Push(static_cast<T>(val));
  return RunResult::Ok;
}

template <typename T, typename V>
RunResult Thread::DoStore(Instr instr, Trap::Ptr* out_trap) {
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32x2.fst]};
  V val = static_cast<V>(Pop<T>());
  u64 offset = PopPtr(memory);
  TRAP_IF(Failed(memory->Store(offset, instr.imm_u32x2.snd, val)),
          StringPrintf("out of bounds memory access: access at %" PRIu64
                       "+%" PRIzd " >= max value %" PRIu64,
                       offset + instr.imm_u32x2.snd, sizeof(V),
                       memory->ByteSize()));
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoUnop(UnopFunc<R, T> f) {
  Push<R>(f(Pop<T>()));
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoUnop(UnopTrapFunc<R, T> f, Trap::Ptr* out_trap) {
  T out;
  std::string msg;
  TRAP_IF(f(Pop<T>(), &out, &msg) == RunResult::Trap, msg);
  Push<R>(out);
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoBinop(BinopFunc<R, T> f) {
  auto rhs = Pop<T>();
  auto lhs = Pop<T>();
  Push<R>(f(lhs, rhs));
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoBinop(BinopTrapFunc<R, T> f, Trap::Ptr* out_trap) {
  auto rhs = Pop<T>();
  auto lhs = Pop<T>();
  T out;
  std::string msg;
  TRAP_IF(f(lhs, rhs, &out, &msg) == RunResult::Trap, msg);
  Push<R>(out);
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoConvert(Trap::Ptr* out_trap) {
  auto val = Pop<T>();
  if (std::is_integral<R>::value && std::is_floating_point<T>::value) {
    // Don't use std::isnan here because T may be a non-floating-point type.
    TRAP_IF(IsNaN(val), "invalid conversion to integer");
  }
  TRAP_UNLESS(CanConvert<R>(val), "integer overflow");
  Push<R>(Convert<R>(val));
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoReinterpret() {
  Push(Bitcast<R>(Pop<T>()));
  return RunResult::Ok;
}

RunResult Thread::DoMemoryInit(Instr instr, Trap::Ptr* out_trap) {
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32x2.fst]};
  auto&& data = inst_->datas()[instr.imm_u32x2.snd];
  auto size = Pop<u32>();
  auto src = Pop<u32>();
  auto dst = PopPtr(memory);
  TRAP_IF(Failed(memory->Init(dst, data, src, size)),
          "out of bounds memory access: memory.init out of bounds");
  return RunResult::Ok;
}

RunResult Thread::DoDataDrop(Instr instr) {
  inst_->datas()[instr.imm_u32].Drop();
  return RunResult::Ok;
}

RunResult Thread::DoMemoryCopy(Instr instr, Trap::Ptr* out_trap) {
  Memory::Ptr mem_dst{store_, inst_->memories()[instr.imm_u32x2.fst]};
  Memory::Ptr mem_src{store_, inst_->memories()[instr.imm_u32x2.snd]};
  auto size = PopPtr(mem_src);
  auto src = PopPtr(mem_src);
  auto dst = PopPtr(mem_dst);
  // TODO: change to "out of bounds"
  TRAP_IF(Failed(Memory::Copy(*mem_dst, dst, *mem_src, src, size)),
          "out of bounds memory access: memory.copy out of bound");
  return RunResult::Ok;
}

RunResult Thread::DoMemoryFill(Instr instr, Trap::Ptr* out_trap) {
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32]};
  auto size = PopPtr(memory);
  auto value = Pop<u32>();
  auto dst = PopPtr(memory);
  TRAP_IF(Failed(memory->Fill(dst, value, size)),
          "out of bounds memory access: memory.fill out of bounds");
  return RunResult::Ok;
}

RunResult Thread::DoTableInit(Instr instr, Trap::Ptr* out_trap) {
  Table::Ptr table{store_, inst_->tables()[instr.imm_u32x2.fst]};
  auto&& elem = inst_->elems()[instr.imm_u32x2.snd];
  auto size = Pop<u32>();
  auto src = Pop<u32>();
  auto dst = Pop<u32>();
  TRAP_IF(Failed(table->Init(store_, dst, elem, src, size)),
          "out of bounds table access: table.init out of bounds");
  return RunResult::Ok;
}

RunResult Thread::DoElemDrop(Instr instr) {
  inst_->elems()[instr.imm_u32].Drop();
  return RunResult::Ok;
}

RunResult Thread::DoTableCopy(Instr instr, Trap::Ptr* out_trap) {
  Table::Ptr table_dst{store_, inst_->tables()[instr.imm_u32x2.fst]};
  Table::Ptr table_src{store_, inst_->tables()[instr.imm_u32x2.snd]};
  auto size = Pop<u32>();
  auto src = Pop<u32>();
  auto dst = Pop<u32>();
  TRAP_IF(Failed(Table::Copy(store_, *table_dst, dst, *table_src, src, size)),
          "out of bounds table access: table.copy out of bounds");
  return RunResult::Ok;
}

RunResult Thread::DoTableGet(Instr instr, Trap::Ptr* out_trap) {
  Table::Ptr table{store_, inst_->tables()[instr.imm_u32]};
  auto index = Pop<u32>();
  Ref ref;
  TRAP_IF(Failed(table->Get(index, &ref)),
          StringPrintf(
              "out of bounds table access: table.get at %u >= max value %u",
              index, table->size()));
  Push(ref);
  return RunResult::Ok;
}

RunResult Thread::DoTableSet(Instr instr, Trap::Ptr* out_trap) {
  Table::Ptr table{store_, inst_->tables()[instr.imm_u32]};
  auto ref = Pop<Ref>();
  auto index = Pop<u32>();
  TRAP_IF(Failed(table->Set(store_, index, ref)),
          StringPrintf(
              "out of bounds table access: table.set at %u >= max value %u",
              index, table->size()));
  return RunResult::Ok;
}

RunResult Thread::DoTableGrow(Instr instr, Trap::Ptr* out_trap) {
  Table::Ptr table{store_, inst_->tables()[instr.imm_u32]};
  u32 old_size = table->size();
  auto delta = Pop<u32>();
  auto ref = Pop<Ref>();
  if (Failed(table->Grow(store_, delta, ref))) {
    Push<s32>(-1);
  } else {
    Push<u32>(old_size);
  }
  return RunResult::Ok;
}

RunResult Thread::DoTableSize(Instr instr) {
  Table::Ptr table{store_, inst_->tables()[instr.imm_u32]};
  Push<u32>(table->size());
  return RunResult::Ok;
}

RunResult Thread::DoTableFill(Instr instr, Trap::Ptr* out_trap) {
  Table::Ptr table{store_, inst_->tables()[instr.imm_u32]};
  auto size = Pop<u32>();
  auto value = Pop<Ref>();
  auto dst = Pop<u32>();
  TRAP_IF(Failed(table->Fill(store_, dst, value, size)),
          "out of bounds table access: table.fill out of bounds");
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoSimdSplat() {
  auto val = Pop<T>();
  R result;
  std::fill(std::begin(result.v), std::end(result.v), val);
  Push(result);
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoSimdExtract(Instr instr) {
  Push<T>(Pop<R>()[instr.imm_u8]);
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoSimdReplace(Instr instr) {
  auto val = Pop<T>();
  auto simd = Pop<R>();
  simd[instr.imm_u8] = val;
  Push(simd);
  return RunResult::Ok;
}

template <typename T> struct Simd128;
template <> struct Simd128<s8> { using Type = s8x16; };
template <> struct Simd128<u8> { using Type = u8x16; };
template <> struct Simd128<s16> { using Type = s16x8; };
template <> struct Simd128<u16> { using Type = u16x8; };
template <> struct Simd128<s32> { using Type = s32x4; };
template <> struct Simd128<u32> { using Type = u32x4; };
template <> struct Simd128<s64> { using Type = s64x2; };
template <> struct Simd128<u64> { using Type = u64x2; };
template <> struct Simd128<f32> { using Type = f32x4; };
template <> struct Simd128<f64> { using Type = f64x2; };

template <typename R, typename T>
RunResult Thread::DoSimdUnop(UnopFunc<R, T> f) {
  using ST = typename Simd128<T>::Type;
  using SR = typename Simd128<R>::Type;
  auto val = Pop<ST>();
  SR result;
  std::transform(std::begin(val.v), std::end(val.v), std::begin(result.v), f);
  Push(result);
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoSimdUnopZero(UnopFunc<R, T> f) {
  using ST = typename Simd128<T>::Type;
  using SR = typename Simd128<R>::Type;
  auto val = Pop<ST>();
  SR result;
  for (u8 i = 0; i < ST::lanes; ++i) {
    result[i] = f(val[i]);
  }
  for (u8 i = ST::lanes; i < SR::lanes; ++i) {
    result[i] = 0;
  }
  Push(result);
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoSimdBinop(BinopFunc<R, T> f) {
  using ST = typename Simd128<T>::Type;
  using SR = typename Simd128<R>::Type;
  static_assert(ST::lanes == SR::lanes, "SIMD lanes don't match");
  auto rhs = Pop<ST>();
  auto lhs = Pop<ST>();
  SR result;
  for (u8 i = 0; i < SR::lanes; ++i) {
    result[i] = f(lhs[i], rhs[i]);
  }
  Push(result);
  return RunResult::Ok;
}

RunResult Thread::DoSimdBitSelect() {
  using S = u64x2;
  auto c = Pop<S>();
  auto rhs = Pop<S>();
  auto lhs = Pop<S>();
  S result;
  for (u8 i = 0; i < S::lanes; ++i) {
    result[i] = (lhs[i] & c[i]) | (rhs[i] & ~c[i]);
  }
  Push(result);
  return RunResult::Ok;
}

template <typename S, u8 count>
RunResult Thread::DoSimdIsTrue() {
  using L = typename S::LaneType;
  auto val = Pop<S>();
  Push(std::count_if(std::begin(val.v), std::end(val.v),
                     [](L x) { return x != 0; }) >= count);
  return RunResult::Ok;
}

template <typename S>
RunResult Thread::DoSimdBitmask() {
  auto val = Pop<S>();
  u32 result = 0;
  for (u8 i = 0; i < S::lanes; ++i) {
    if (val[i] < 0) {
      result |= 1 << i;
    }
  }
  Push(result);
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoSimdShift(BinopFunc<R, T> f) {
  using ST = typename Simd128<T>::Type;
  using SR = typename Simd128<R>::Type;
  static_assert(ST::lanes == SR::lanes, "SIMD lanes don't match");
  auto amount = Pop<u32>();
  auto lhs = Pop<ST>();
  SR result;
  for (u8 i = 0; i < SR::lanes; ++i) {
    result[i] = f(lhs[i], amount);
  }
  Push(result);
  return RunResult::Ok;
}

template <typename S>
RunResult Thread::DoSimdLoadSplat(Instr instr, Trap::Ptr* out_trap) {
  using L = typename S::LaneType;
  L val;
  if (Load<L>(instr, &val, out_trap) != RunResult::Ok) {
    return RunResult::Trap;
  }
  S result;
  std::fill(std::begin(result.v), std::end(result.v), val);
  Push(result);
  return RunResult::Ok;
}

template <typename S>
RunResult Thread::DoSimdLoadLane(Instr instr, Trap::Ptr* out_trap) {
  using T = typename S::LaneType;
  auto result = Pop<S>();
  T val;
  if (Load<T>(instr, &val, out_trap) != RunResult::Ok) {
    return RunResult::Trap;
  }
  result[instr.imm_u32x2_u8.idx] = val;
  Push(result);
  return RunResult::Ok;
}

template <typename S>
RunResult Thread::DoSimdStoreLane(Instr instr, Trap::Ptr* out_trap) {
  using T = typename S::LaneType;
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32x2_u8.fst]};
  auto result = Pop<S>();
  T val = result[instr.imm_u32x2_u8.idx];
  u64 offset = PopPtr(memory);
  TRAP_IF(Failed(memory->Store(offset, instr.imm_u32x2_u8.snd, val)),
          StringPrintf("out of bounds memory access: access at %" PRIu64
                       "+%" PRIzd " >= max value %" PRIu64,
                       offset + instr.imm_u32x2_u8.snd, sizeof(T),
                       memory->ByteSize()));
  return RunResult::Ok;
}

template <typename S, typename T>
RunResult Thread::DoSimdLoadZero(Instr instr, Trap::Ptr* out_trap) {
  using L = typename S::LaneType;
  L val;
  if (Load<L>(instr, &val, out_trap) != RunResult::Ok) {
    return RunResult::Trap;
  }
  S result;
  std::fill(std::begin(result.v), std::end(result.v), 0);
  result[0] = val;
  Push(result);
  return RunResult::Ok;
}

RunResult Thread::DoSimdSwizzle() {
  using S = u8x16;
  auto rhs = Pop<S>();
  auto lhs = Pop<S>();
  S result;
  for (u8 i = 0; i < S::lanes; ++i) {
    result[i] = rhs[i] < S::lanes ? lhs[rhs[i]] : 0;
  }
  Push(result);
  return RunResult::Ok;
}

RunResult Thread::DoSimdShuffle(Instr instr) {
  using S = u8x16;
  auto sel = Bitcast<S>(instr.imm_v128);
  auto rhs = Pop<S>();
  auto lhs = Pop<S>();
  S result;
  for (u8 i = 0; i < S::lanes; ++i) {
    result[i] = sel[i] < S::lanes ? lhs[sel[i]] : rhs[sel[i] - S::lanes];
  }
  Push(result);
  return RunResult::Ok;
}

template <typename S, typename T>
RunResult Thread::DoSimdNarrow() {
  using SL = typename S::LaneType;
  using TL = typename T::LaneType;
  auto rhs = Pop<T>();
  auto lhs = Pop<T>();
  S result;
  for (u8 i = 0; i < T::lanes; ++i) {
    result[i] = Saturate<SL, TL>(lhs[i]);
  }
  for (u8 i = 0; i < T::lanes; ++i) {
    result[T::lanes + i] = Saturate<SL, TL>(rhs[i]);
  }
  Push(result);
  return RunResult::Ok;
}

template <typename S, typename T, bool low>
RunResult Thread::DoSimdConvert() {
  using SL = typename S::LaneType;
  auto val = Pop<T>();
  S result;
  for (u8 i = 0; i < S::lanes; ++i) {
    result[i] = Convert<SL>(val[(low ? 0 : S::lanes) + i]);
  }
  Push(result);
  return RunResult::Ok;
}

template <typename S, typename T, bool low>
RunResult Thread::DoSimdExtmul() {
  auto rhs = Pop<T>();
  auto lhs = Pop<T>();
  S result;
  using U = typename S::LaneType;
  for (u8 i = 0; i < S::lanes; ++i) {
    u8 laneidx = (low ? 0 : S::lanes) + i;
    result[i] = U(lhs[laneidx]) * U(rhs[laneidx]);
  }
  Push(result);
  return RunResult::Ok;
}

template <typename S, typename T>
RunResult Thread::DoSimdLoadExtend(Instr instr, Trap::Ptr* out_trap) {
  T val;
  if (Load<T>(instr, &val, out_trap) != RunResult::Ok) {
    return RunResult::Trap;
  }
  S result;
  for (u8 i = 0; i < S::lanes; ++i) {
    result[i] = val[i];
  }
  Push(result);
  return RunResult::Ok;
}

template <typename S, typename T>
RunResult Thread::DoSimdExtaddPairwise() {
  auto val = Pop<T>();
  S result;
  using U = typename S::LaneType;
  for (u8 i = 0; i < S::lanes; ++i) {
    u8 laneidx = i * 2;
    result[i] = U(val[laneidx]) + U(val[laneidx + 1]);
  }
  Push(result);
  return RunResult::Ok;
}

template <typename S, typename T>
RunResult Thread::DoSimdDot() {
  using SL = typename S::LaneType;
  auto rhs = Pop<T>();
  auto lhs = Pop<T>();
  S result;
  for (u8 i = 0; i < S::lanes; ++i) {
    u8 laneidx = i * 2;
    SL lo = SL(lhs[laneidx]) * SL(rhs[laneidx]);
    SL hi = SL(lhs[laneidx + 1]) * SL(rhs[laneidx + 1]);
    result[i] = Add(lo, hi);
  }
  Push(result);
  return RunResult::Ok;
}

template <typename T, typename V>
RunResult Thread::DoAtomicLoad(Instr instr, Trap::Ptr* out_trap) {
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32x2.fst]};
  u64 offset = PopPtr(memory);
  V val;
  TRAP_IF(Failed(memory->AtomicLoad(offset, instr.imm_u32x2.snd, &val)),
          StringPrintf("invalid atomic access at %" PRIaddress "+%u", offset,
                       instr.imm_u32x2.snd));
  Push(static_cast<T>(val));
  return RunResult::Ok;
}

template <typename T, typename V>
RunResult Thread::DoAtomicStore(Instr instr, Trap::Ptr* out_trap) {
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32x2.fst]};
  V val = static_cast<V>(Pop<T>());
  u64 offset = PopPtr(memory);
  TRAP_IF(Failed(memory->AtomicStore(offset, instr.imm_u32x2.snd, val)),
          StringPrintf("invalid atomic access at %" PRIaddress "+%u", offset,
                       instr.imm_u32x2.snd));
  return RunResult::Ok;
}

template <typename R, typename T>
RunResult Thread::DoAtomicRmw(BinopFunc<T, T> f,
                              Instr instr,
                              Trap::Ptr* out_trap) {
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32x2.fst]};
  T val = static_cast<T>(Pop<R>());
  u64 offset = PopPtr(memory);
  T old;
  TRAP_IF(Failed(memory->AtomicRmw(offset, instr.imm_u32x2.snd, val, f, &old)),
          StringPrintf("invalid atomic access at %" PRIaddress "+%u", offset,
                       instr.imm_u32x2.snd));
  Push(static_cast<R>(old));
  return RunResult::Ok;
}

template <typename T, typename V>
RunResult Thread::DoAtomicRmwCmpxchg(Instr instr, Trap::Ptr* out_trap) {
  Memory::Ptr memory{store_, inst_->memories()[instr.imm_u32x2.fst]};
  V replace = static_cast<V>(Pop<T>());
  V expect = static_cast<V>(Pop<T>());
  V old;
  u64 offset = PopPtr(memory);
  TRAP_IF(Failed(memory->AtomicRmwCmpxchg(offset, instr.imm_u32x2.snd, expect,
                                          replace, &old)),
          StringPrintf("invalid atomic access at %" PRIaddress "+%u", offset,
                       instr.imm_u32x2.snd));
  Push(static_cast<T>(old));
  return RunResult::Ok;
}

RunResult Thread::DoThrow(Exception::Ptr exn) {
  Istream::Offset target_offset = Istream::kInvalidOffset;
  u32 target_values, target_exceptions;
  Tag::Ptr exn_tag{store_, exn->tag()};
  bool popped_frame = false;
  bool had_catch_all = false;

  // DoThrow is responsible for unwinding the stack at the point at which an
  // exception is thrown, and also branching to the appropriate catch within
  // the target try-catch. In a compiler, the tag dispatch might be done in
  // generated code in a landing pad, but this is easier for the interpreter.
  while (!frames_.empty()) {
    const Frame& frame = frames_.back();
    DefinedFunc::Ptr func{store_, frame.func};
    u32 pc = frame.offset;
    auto handlers = func->desc().handlers;

    // We iterate in reverse order, in order to traverse handlers from most
    // specific (pushed last) to least specific within a nested stack of
    // try-catch blocks.
    auto iter = handlers.rbegin();
    while (iter != handlers.rend()) {
      const HandlerDesc& handler = *iter;
      if (pc >= handler.try_start_offset && pc < handler.try_end_offset) {
        // For a try-delegate, skip part of the traversal by directly going
        // up to an outer handler specified by the delegate depth.
        if (handler.kind == HandlerKind::Delegate) {
          // Subtract one as we're trying to get a reverse iterator that is
          // offset by `delegate_handler_index` from the first item.
          iter = handlers.rend() - handler.delegate_handler_index - 1;
          continue;
        }
        // Otherwise, check for a matching catch tag or catch_all.
        for (auto _catch : handler.catches) {
          // Here we have to be careful to use the target frame's instance
          // to look up the tag rather than the throw's instance.
          Ref catch_tag_ref = frame.inst->tags()[_catch.tag_index];
          Tag::Ptr catch_tag{store_, catch_tag_ref};
          if (exn_tag == catch_tag) {
            target_offset = _catch.offset;
            target_values = (*iter).values;
            target_exceptions = (*iter).exceptions;
            goto found_handler;
          }
        }
        if (handler.catch_all_offset != Istream::kInvalidOffset) {
          target_offset = handler.catch_all_offset;
          target_values = (*iter).values;
          target_exceptions = (*iter).exceptions;
          had_catch_all = true;
          goto found_handler;
        }
      }
      iter++;
    }
    frames_.pop_back();
    popped_frame = true;
  }

  // If the call frames are empty now, the exception is uncaught.
  assert(frames_.empty());
  return RunResult::Exception;

found_handler:
  assert(target_offset != Istream::kInvalidOffset);

  Frame& target_frame = frames_.back();
  // If the throw crosses call frames, we need to reset the state to that
  // call frame's values. The stack heights may need to be offset by the
  // handler's heights as we may be jumping into the middle of the function
  // code after some stack height changes.
  if (popped_frame) {
    inst_ = target_frame.inst;
    mod_ = target_frame.mod;
  }
  values_.resize(target_frame.values + target_values);
  exceptions_.resize(target_frame.exceptions + target_exceptions);
  // Jump to the handler.
  target_frame.offset = target_offset;
  // When an exception is caught, it needs to be tracked in a stack
  // to allow for rethrows. This stack is popped on leaving the try-catch
  // or by control instructions such as `br`.
  exceptions_.push_back(exn.ref());
  // Also push exception payload values if applicable.
  if (!had_catch_all) {
    PushValues(exn_tag->type().signature, exn->args());
  }
  return RunResult::Ok;
}

Thread::TraceSource::TraceSource(Thread* thread) : thread_(thread) {}

std::string Thread::TraceSource::Header(Istream::Offset offset) {
  return StringPrintf("#%" PRIzd ". %4u: V:%-3" PRIzd,
                      thread_->frames_.size() - 1, offset,
                      thread_->values_.size());
}

std::string Thread::TraceSource::Pick(Index index, Instr instr) {
  Value val = thread_->Pick(index);
  const char* reftype;
  // Estimate number of operands.
  // TODO: Instead, record this accurately in opcode.def.
  Index num_operands = 3;
  for (Index i = 3; i >= 1; i--) {
    if (instr.op.GetParamType(i) == ValueType::Void) {
      num_operands--;
    } else {
      break;
    }
  }
  auto type = index > num_operands
                  ? Type(ValueType::Void)
                  : instr.op.GetParamType(num_operands - index + 1);
  if (type == ValueType::Void) {
    // Void should never be displayed normally; we only expect to see it when
    // the stack may have different a different type. This is likely to occur
    // with an index; try to see which type we should expect.
    switch (instr.op) {
      case Opcode::GlobalSet: type = GetGlobalType(instr.imm_u32); break;
      case Opcode::LocalSet:
      case Opcode::LocalTee:  type = GetLocalType(instr.imm_u32); break;
      case Opcode::TableSet:
      case Opcode::TableGrow:
      case Opcode::TableFill: type = GetTableElementType(instr.imm_u32); break;
      default: return "?";
    }
  }

  switch (type) {
    case ValueType::I32: return StringPrintf("%u", val.Get<u32>());
    case ValueType::I64: return StringPrintf("%" PRIu64, val.Get<u64>());
    case ValueType::F32: return StringPrintf("%g", val.Get<f32>());
    case ValueType::F64: return StringPrintf("%g", val.Get<f64>());
    case ValueType::V128: {
      auto v = val.Get<v128>();
      return StringPrintf("0x%08x 0x%08x 0x%08x 0x%08x", v.u32(0), v.u32(1),
                          v.u32(2), v.u32(3));
    }

    case ValueType::FuncRef:    reftype = "funcref"; break;
    case ValueType::ExternRef:  reftype = "externref"; break;

    default:
      WABT_UNREACHABLE;
      break;
  }

  // Handle ref types.
  return StringPrintf("%s:%" PRIzd, reftype, val.Get<Ref>().index);
}

ValueType Thread::TraceSource::GetLocalType(Index stack_slot) {
  const Frame& frame = thread_->frames_.back();
  DefinedFunc::Ptr func{thread_->store_, frame.func};
  // When a function is called, the arguments are first pushed on the stack by
  // the caller, then the new call frame is pushed (which caches the current
  // height of the value stack). At that point, any local variables will be
  // allocated on the stack. For example, a function that has two parameters
  // and one local variable will have a stack like this:
  //
  //                 frame.values      top of stack
  //                 v                 v
  //   param1 param2 | local1 ..........
  //
  // When the instruction stream is generated, all local variable access is
  // translated into a value relative to the top of the stack, counting up from
  // 1. So in the previous example, if there are three values above the local
  // variable, the stack looks like:
  //
  //              param1 param2 | local1 value1 value2 value3
  // stack slot:    6      5        4      3      2      1
  // local index:   0      1        2
  //
  // local1 can be accessed with stack_slot 4, and param1 can be accessed with
  // stack_slot 6. The formula below takes these values into account to convert
  // the stack_slot into a local index.
  Index local_index =
      (thread_->values_.size() - frame.values + func->type().params.size()) -
      stack_slot;
  return func->desc().GetLocalType(local_index);
}

ValueType Thread::TraceSource::GetGlobalType(Index index) {
  return thread_->mod_->desc().globals[index].type.type;
}

ValueType Thread::TraceSource::GetTableElementType(Index index) {
  return thread_->mod_->desc().tables[index].type.element;
}

}  // namespace interp
}  // namespace wabt
