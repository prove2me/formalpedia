-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:12:26.867377+00:00
-- url     : https://prove2.me/submissions/070865ac-ea48-4a69-b0e4-0e006e9f06c7

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S158
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_Clause_callback_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LeafProgram_Factor_marked_tail_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed record-control code for sparse-hash evaluation. This module fixes
all parsing and traversal code. Arithmetic components below are finite native
commands, to be instantiated by the separate dictionary modules; no semantic
function is called by the machine. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem copy_eval (d : Machine) (src dst tmp : Fin 96)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : d.stacks tmp = []) :
    Eval (copy src dst tmp) (7*(d.stacks src).length+5) d (copied d src dst) := by
  apply Eval.call
  have h := StackRoutines.copyProgram_trace src dst tmp (0 : Fin 8) 1 hsd hst htd
    (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ h 7 rfl rfl
  simpa [copied,StackRoutines.copyResult,StructuredProgram.State.withPC,
    StackRoutines.copyProgram,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Split-memory rules for composing the actual low arithmetic workspace with
persistent high interpreter data. All movement lemmas retain primitive costs. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem high_injective : Function.Injective highPort := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change 56+i.val = 56+j.val at hh
  omega

theorem low_ne_high (i : Fin 56) (j : Fin 40) : lowPort i ≠ highPort j := by
  intro h
  have hh := congrArg Fin.val h
  change i.val = 56+j.val at hh
  omega

theorem update_high (low high) (i : Fin 40) (word : List Bool) :
    Function.update (tapes low high) (highPort i) word = tapes low (Function.update high i word) := by
  funext j
  induction j using (Fin.addCases (m := 56) (n := 40)) with
  | left j =>
    change (Function.update (tapes low high) (highPort i) word) (lowPort j) =
      tapes low (Function.update high i word) (lowPort j)
    simp [low_ne_high j i]
  | right j =>
    change (Function.update (tapes low high) (highPort i) word) (highPort j) =
      tapes low (Function.update high i word) (highPort j)
    by_cases hj : j = i
    · subst j; simp
    · have hh : highPort j ≠ highPort i := fun h => hj (high_injective h)
      simp [hh,hj]

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramArithmeticNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


/-! Component: HashCircuitProgramArithmetic. All public namespaces and APIs are retained. -/


/-! Native arithmetic wiring for the hash interpreter. Scale and normalized
addition are fixed imported instruction tables. Product is wired separately
when the native product table is supplied by its implementation module. -/

/-! Component: HashCircuitProgram. All public namespaces and APIs are retained. -/


/-! The fixed native sparse-hash row instruction table. All arithmetic
components are now concrete native programs: there are no operation-valued
parameters in `command` or `program`. The complete serialized semantic and
primitive-time theorem must additionally discharge the local callback
contracts for this table; no such theorem is asserted merely by compilation. -/

/-! Component: HashCircuitProgramMemoryExtra. All public namespaces and APIs are retained. -/


namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- Preserving copy between persistent interpreter words. -/
theorem copy_high_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool)
    (high : Fin 40 → List Bool) (src dst tmp : Fin 40)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (htmp : high tmp = []) :
    Eval (copy (highPort src) (highPort dst) (highPort tmp)) (7*(high src).length+5)
      (state regs low high)
      (state (readRegs regs 0 1 none) low (Function.update high dst (high src ++ high dst))) := by
  have h := Native.copy_eval (state regs low high) (highPort src) (highPort dst) (highPort tmp)
    (fun he => hsd (high_injective he)) (fun he => hst (high_injective he))
    (fun he => htd (high_injective he)) (by simpa [state] using htmp)
  simpa only [state,copied,StackRoutines.copyStacks,tapes_high,update_high] using h

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

/-! Component: HashCircuitProgramWeightedCallbacks. All public namespaces and APIs are retained. -/


/-! The two concrete weighted arithmetic adapters used by the hash evaluator.
The statements expose exact dictionary bytes and restoration of the common
arithmetic workspace. In particular they do not assume callback correctness. -/

/-! Component: HashCircuitProgramProduct. All public namespaces and APIs are retained. -/


/-! Concrete product callback refinement. Both sparse operands are copied from
persistent interpreter stacks into the real product program. The result is
copied back, and all temporary operands are physically reclaimed. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramDynamicFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured physical record fold with accumulator-dependent cost. This
retains the actual fixed callback and parser; the cost recurrence can account
for changing sparse dictionary lengths without postulating a uniform bound. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.RecordPrograms

variable {r s : ℕ} {R A : Type*}

theorem loop_eval (p : Ports r s) (callback : Cmd r s) (encode : R → List Bool)
    (step : R → A → A) (cost : R → A → ℕ) (Rep : A → State r s → Prop)
    (hc : Contract p callback encode step cost Rep)
    (xs : List R) (a : A) (base : State r s) (hb : Rep a base) (suffix : List Bool) :
    ∃ n next, n ≤ 1+work encode step cost xs a ∧ Rep (value step xs a) next ∧
      Eval (loop p callback) n (afterTag p base (xs.map encode) suffix)
        (state p next false true false suffix []) := by
  induction xs generalizing a base with
  | nil =>
    refine ⟨1,base,by simp [work],hb,?_⟩
    apply Eval.while_false
    simp [afterTag]
  | cons x xs ih =>
    let tail := Encoding.encodeList id (xs.map encode) ++ suffix
    obtain ⟨n,middle,hn,hm,hcallback⟩ := hc x a base hb tail
    have hreader : Eval (reader p) (6*(encode x).length+4)
        (afterTag p base ((x::xs).map encode) suffix)
        (state p base false true false tail (encode x).reverse) := by
      simpa [afterTag,tail] using reader_eval p base (encode x) tail [] true true false
    have hguard : (afterTag p base ((x::xs).map encode) suffix).regs p.tag = true := by
      simp [afterTag]
    have hbranch : Eval (.ite p.found (atom (.set p.tag false))
        (atom (.pop p.source p.tag p.present))) 2
        (state p middle false true false tail [])
        (afterTag p middle (xs.map encode) suffix) := by
      apply Eval.ite_false (by simp)
      exact pop_list_eval p middle (xs.map encode) suffix false true
    obtain ⟨m,next,hmb,hr,hrest⟩ := ih (step x a) middle hm
    have run := Eval.while_true hguard (hreader.seq (hcallback.seq hbranch)) hrest
    refine ⟨(6*(encode x).length+4+(n+2))+m+1,next,?_,hr,?_⟩
    · simp only [work]; omega
    · simpa [loop,body] using run

theorem command_eval (p : Ports r s) (callback : Cmd r s) (encode : R → List Bool)
    (step : R → A → A) (cost : R → A → ℕ) (Rep : A → State r s → Prop)
    (hc : Contract p callback encode step cost Rep)
    (xs : List R) (a : A) (base : State r s) (hb : Rep a base) (suffix : List Bool)
    (v pr f : Bool) :
    ∃ n next, n ≤ 3+work encode step cost xs a ∧ Rep (value step xs a) next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id (xs.map encode) ++ suffix) [])
        (state p next false true false suffix []) := by
  obtain ⟨n,next,hn,hr,hloop⟩ := loop_eval p callback encode step cost Rep hc xs a base hb suffix
  exact ⟨1+(1+n),next,by omega,hr,
    (set_found_eval p base v pr f false _ []).seq
      ((pop_list_eval p base (xs.map encode) suffix v pr).seq hloop)⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.DynamicFold

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramInterpreter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff


/-! Component: HashCircuitProgramLiteralCallback. All public namespaces and APIs are retained. -/


/-! Literal callback with actual lookup, polarity, sparse product, and return.
The represented minus-one and one values are explicit cached inputs. All work
is performed by the fixed native commands wired into the row interpreter. -/

/-! Component: HashCircuitProgramClause. All public namespaces and APIs are retained. -/


/-! Typed clause traversal using the fixed native literal callback. Input is
still the original unary literal encoding; the type is used only to specify
which dictionary entry the native decoder and lookup retrieve. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem record_state (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool)
    (acc src payload : List Bool) (v pr f : Bool) :
    RecordPrograms.state literalPorts (base regs e high acc) v pr f src payload =
      Memory.state (Function.update (Function.update (Function.update regs 0 v) 1 pr) 2 f)
        (Product.tapes e) (recordHigh high acc src payload) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.update (Function.update (Memory.tapes (Product.tapes e) (baseHigh high acc))
      (Memory.highPort 7) src) (Memory.highPort 2) payload =
      Memory.tapes (Product.tapes e) (recordHigh high acc src payload)
    rw [Memory.update_high,Memory.update_high]
    rfl

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

/-- The fixed clause loop visits every original literal. Its cost recurrence
includes every physical frame read, arithmetic callback and loop branch. -/
theorem command_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (ls : List (SAT.Literal (Fin n))) (acc : List (Product.Entry n (baseWidth p t) d))
    (suffix : List Bool) (v pr f : Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    let update := step p t M cache table minusOne one incidence u J
    ∃ k ≤ 3+DynamicFold.work literalBits update (cost p t M cache table minusOne one incidence degree u J entries) ls acc,
      ∃ rr, Eval (clauseLoop arithmetic) k
        (RecordPrograms.state literalPorts (base regs e high (Product.bytes acc)) v pr f
          (Encoding.encodeList id (ls.map literalBits) ++ suffix) [])
        (RecordPrograms.state literalPorts
          (base rr e high (Product.bytes (DynamicFold.value update ls acc))) false true false suffix []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let update := step p t M cache table minusOne one incidence u J
  let charge := cost p t M cache table minusOne one incidence degree u J entries
  let Rep : List (Product.Entry n (baseWidth p t) d) → Machine → Prop :=
    fun a b => ∃ rr, b = base rr e high (Product.bytes a)
  have hc : DynamicFold.Contract literalPorts (literalStep arithmetic) literalBits update charge Rep := by
    intro l a b hb tail
    obtain ⟨rflRegs,rfl⟩ := hb
    obtain ⟨k,hk,rr,he⟩ := callback_eval p t M cache table minusOne one incidence degree u J entries
      hz width hd hw hl rflRegs high ht ho hm htmp l a tail
    exact ⟨k,base rr e high (Product.bytes (update l a)),hk,⟨rr,rfl⟩,he⟩
  obtain ⟨k,next,hk,hn,he⟩ := DynamicFold.command_eval literalPorts (literalStep arithmetic) literalBits
    update charge Rep hc ls acc (base regs e high (Product.bytes acc)) ⟨regs,rfl⟩ suffix v pr f
  obtain ⟨rr,rfl⟩ := hn
  exact ⟨k,hk,rr,he⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Clause

/-! Component: HashCircuitProgramRow. All public namespaces and APIs are retained. -/


/-! The actual nested hash-row interpreter. The only inputs below are serialized
literal clauses, flat represented scalars, the selected incidence dictionary,
and the ring/cache words used by the native services. -/

/-! Component: HashCircuitProgramRun. All public namespaces and APIs are retained. -/


/-! Compiled fixed-program trace for one serialized sparse hash row. The
initial accumulator is physically cleared, and the final halt is charged. -/

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClause
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Evaluate the optional marked clause without applying a hash idempotent.
The constant seed is copied by the machine, and every original literal is
processed by the same concrete decoder and sparse arithmetic as hash rows. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Clause

open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open MomentsProgram

theorem command_eval (p t : ℕ) [Fact p.Prime]
    (M : SubexpPreparedQuartic.Modulus p t) (cache : RingProgram.ScalarCache p t)
    (hz : BinaryArithmetic.toNat cache.zero.val < p^t) {n d : ℕ}
    (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : List (Product.Entry n (baseWidth p t) d))
    (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
    (degree width : List Bool) (u J : ℕ)
    (hd : degree.length=d) (hw : width.length=baseWidth p t)
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6=Squarefree.Program.lookupRecords entries)
    (ho : high 13=Product.bytes one) (hm : high 20=RingProgram.flat minus)
    (htmp : high 14=[])
    (ls : List (SAT.Literal (Fin n))) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
      degree (List.replicate u true) (List.replicate J true)
    let update := HashCircuitProgram.Native.Clause.step p t M cache table minus one incidence u J
    ∃ k rr, k ≤ 7*(Product.bytes one).length+8+
        DynamicFold.work HashCircuitProgram.Native.Clause.literalBits update
          (HashCircuitProgram.Native.Clause.cost p t M cache table minus one incidence degree u J entries)
          ls one ∧
      Eval command k
        (Memory.state regs (Product.tapes e)
          (HashCircuitProgram.Native.Clause.recordHigh high []
            (Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits)) []))
        (RecordPrograms.state literalPorts
          (HashCircuitProgram.Native.Clause.base rr e high (Product.bytes (DynamicFold.value update ls one)))
          false true false [] []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table)
    degree (List.replicate u true) (List.replicate J true)
  let source := Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits)
  let h0 := HashCircuitProgram.Native.Clause.recordHigh high [] source []
  let h1 := Function.update h0 (11 : Fin 40) (Product.bytes one)
  let r1 := readRegs regs 0 1 none
  have hc := Memory.copy_high_high regs (Product.tapes e) h0 13 11 14
    (by decide) (by decide) (by decide)
    (by
      change high 14 = []
      exact htmp)
  have h13 : h0 13=Product.bytes one := by
    change high 13 = Product.bytes one
    exact ho
  have h11 : h0 11=[] := by
    simp [h0,HashCircuitProgram.Native.Clause.recordHigh,HashCircuitProgram.Native.Clause.baseHigh]
  simp only [h13,h11,List.append_nil] at hc
  obtain ⟨k,hk,rr,he⟩ := HashCircuitProgram.Native.Clause.command_eval p t M cache table minus one
    incidence degree u J entries hz width hd hw hl r1 high ht ho hm htmp ls one []
      (r1 0) (r1 1) (r1 2)
  have hi : RecordPrograms.state literalPorts
      (HashCircuitProgram.Native.Clause.base r1 e high (Product.bytes one))
      (r1 0) (r1 1) (r1 2) (source++[]) [] =
        Memory.state r1 (Product.tapes e) h1 := by
    rw [HashCircuitProgram.Native.Clause.record_state]
    apply congrArg₂ StructuredProgram.State.mk
    · simp
    · apply congrArg (Memory.tapes (Product.tapes e))
      funext i
      fin_cases i <;> simp [h1,h0,HashCircuitProgram.Native.Clause.recordHigh,
        HashCircuitProgram.Native.Clause.baseHigh,literalHigh]
  rw [hi] at he
  refine ⟨7*(Product.bytes one).length+5+k,rr,by omega,?_⟩
  exact hc.seq he

end SubexponentialSAT.SqrtLog.LeafProgram.Clause

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Wide native factor arithmetic and paid tape movement. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls


theorem nativeRegisters_injective : Function.Injective nativeRegisters :=
  Fin.castAdd_injective 8 32


end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorServicesBase
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact framing tools for the fixed wide indicator and marked-clause calls.
The functions below only describe states; executable code remains Factor's
already defined finite service tables. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT BitProgram StructuredCalls
open HashCircuitProgram HashCircuitProgram.Native

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

theorem input_tapes (map : Fin 96 → Fin 768) (a : Data) (lo : Fin 56 → List Bool)
    (hlow : ∀ i, a.stacks (map (Memory.lowPort i))=lo i) :
    Memory.tapes lo (high map a) = a.stacks ∘ map := by
  funext i
  induction i using (Fin.addCases (m:=56) (n:=40)) with
  | left i =>
    change Memory.tapes lo (high map a) (Memory.lowPort i)=a.stacks (map (Memory.lowPort i))
    simpa only [Memory.tapes_low] using (hlow i).symm
  | right i =>
    change Memory.tapes lo (high map a) (Memory.highPort i)=a.stacks (map (Memory.highPort i))
    simp only [Memory.tapes_high,high]

theorem clause_high_input (map : Fin 96 → Fin 768) (a : Data) (source : List Bool)
    (hs : a.stacks (map 63)=source)
    (hw : ∀ i∈clauseScratch,a.stacks (map i)=[]) :
    HashCircuitProgram.Native.Clause.recordHigh (high map a) [] source [] = high map a := by
  funext i
  fin_cases i <;> simp [HashCircuitProgram.Native.Clause.recordHigh,
    HashCircuitProgram.Native.Clause.baseHigh,literalHigh,high]
  all_goals first | exact hs | exact hs.symm | (apply hw; decide)

theorem clause_output_tapes (lo : Fin 56 → List Bool) (h : Fin 40 → List Bool)
    (source result : List Bool) :
    Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh h result [] []) =
      Function.update (Function.update
        (Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh h [] source [])) 63 []) 67 result := by
  change _ = Function.update (Function.update
    (Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh h [] source [])) (Memory.highPort 7) [])
      (Memory.highPort 11) result
  rw [Memory.update_high,Memory.update_high]
  apply congrArg (Memory.tapes lo)
  funext i
  fin_cases i <;> simp [HashCircuitProgram.Native.Clause.recordHigh,HashCircuitProgram.Native.Clause.baseHigh,literalHigh]

theorem extend_project (map : Fin 96 → Fin 768) (hm : Function.Injective map) (a : Data) :
    Function.extend map (a.stacks ∘ map) a.stacks = a.stacks := by
  exact congrArg (fun b : Data => b.stacks)
    (embedState_project Factor.nativeRegisters map a Factor.nativeRegisters_injective hm)

theorem clause_embed (a : Data) (rr : Fin 8 → Bool) (lo : Fin 56 → List Bool)
    (source result : List Bool)
    (hi : Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh (high Clause.callerStacks a) [] source [])=
      a.stacks ∘ Clause.callerStacks) :
    embedState Clause.callerRegisters Clause.callerStacks a
      (Memory.state rr lo (HashCircuitProgram.Native.Clause.recordHigh (high Clause.callerStacks a) result [] [])) =
      clauseFinished a rr result := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.extend Clause.callerStacks
      (Memory.tapes lo (HashCircuitProgram.Native.Clause.recordHigh (high Clause.callerStacks a) result [] []))
      a.stacks = _
    rw [clause_output_tapes lo _ source result,hi]
    have hinj : Function.Injective Clause.callerStacks := Fin.castAdd_injective 96 672
    rw [ProgramLinking.extend_update hinj,
      ProgramLinking.extend_update hinj,extend_project]
    rfl
    exact Fin.castAdd_injective 96 672

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorServices
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual wide factor service calls, including the indicator's three parser
register writes, compiled returns, and exact caller frame. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.FactorServices
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

attribute [local simp] Fin.addCases Fin.coe_ofNat_eq_mod Fin.ext_iff

variable {p t n d : ℕ} [Fact p.Prime]

theorem clause_eval (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ls : List (SAT.Literal (Fin n))) (a : Factor.Data)
    (hlow : ∀ i, a.stacks (Clause.callerStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 63=Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (hwork : ∀ i∈clauseScratch,a.stacks (Clause.callerStacks i)=[]) :
    ∃ k rr, k ≤ clauseBudget ctx minus one incidence entries ls ∧
      Eval Clause.caller k a (clauseFinished a rr
        (Product.bytes (clauseResult ctx minus one incidence ls))) := by
  let h := high Clause.callerStacks a
  let source := Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits)
  have hinput : Memory.tapes (low ctx) (HashCircuitProgram.Native.Clause.recordHigh h [] source [])=
      a.stacks ∘ Clause.callerStacks := by
    rw [clause_high_input Clause.callerStacks a source hsource hwork]
    exact input_tapes Clause.callerStacks a (low ctx) hlow
  obtain ⟨k,rr,hk,he⟩ := Clause.command_eval p t ctx.modulus ctx.cache ctx.zeroBound ctx.table
    minus one incidence (List.replicate d true) ctx.width ctx.u ctx.J (by simp) ctx.widthLength
    entries hl (a.regs ∘ Clause.callerRegisters) h
    (by exact htable) (by exact hone) (by exact hminus) (by exact hwork 70 (by decide)) ls
  have hproject : projectState Clause.callerRegisters Clause.callerStacks a=
      Memory.state (a.regs ∘ Clause.callerRegisters) (low ctx)
        (HashCircuitProgram.Native.Clause.recordHigh h [] source []) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · exact hinput.symm
  dsimp only [low,source] at hproject
  rw [← hproject,HashCircuitProgram.Native.Clause.record_state] at he
  let rf := Function.update (Function.update (Function.update rr 0 false) 1 true) 2 false
  have hc := eval_liftCommand_from_state Clause.command 63 67 Clause.callerRegisters
    Clause.callerStacks a (Fin.castAdd_injective 8 32) (Fin.castAdd_injective 96 672) he
  change Eval (liftCommand Clause.command 63 67 Clause.callerRegisters Clause.callerStacks) (k+1) a
    (embedState Clause.callerRegisters Clause.callerStacks a
      (Memory.state rf (low ctx) (HashCircuitProgram.Native.Clause.recordHigh
        (high Clause.callerStacks a) (Product.bytes (clauseResult ctx minus one incidence ls)) [] []))) at hc
  rw [clause_embed a rf (low ctx) source (Product.bytes (clauseResult ctx minus one incidence ls)) hinput] at hc
  exact ⟨k+1,rf,by dsimp [clauseBudget] at *; omega,hc⟩

theorem clause_frame (a : Factor.Data) (rr : Fin 8 → Bool) (result : List Bool)
    (i : Fin 768) (h63 : i≠63) (h67 : i≠67) :
    (clauseFinished a rr result).stacks i=a.stacks i := by
  simp [clauseFinished,h63,h67]

end SubexponentialSAT.SqrtLog.LeafProgram.FactorServices

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramFactorValue
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.FiniteFallback.literalFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Execution of the computed factor value and its multiplication into the
current head product. Input incidence dictionaries are the physically
produced tables supplied by the preceding service. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Factor
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing
open HashCircuitProgram HashCircuitProgram.Native
open IdempotentApplyProgram.Steps
open MomentsProgram

variable {p t n d : ℕ} [Fact p.Prime]

theorem low_ne (i : Fin 56) (j : Fin 768) (hj : 56 ≤ j.val) :
    nativeStacks (Memory.lowPort i)  ≠  j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=j.val at hv
  omega


omit [Fact (Nat.Prime p)] in
private theorem clause_lowReady (ctx : Context p t n d) (a : Data)
    (rr : Fin 8 → Bool) (result : List Bool)
    (hlow : ∀ i,a.stacks (Clause.callerStacks (Memory.lowPort i))=low ctx i) :
    lowReady (FactorServices.clauseFinished a rr result)
      (Product.idle ctx.modulus.bits ctx.width ctx.cache.zero.val
        (RingTriple.tableEncoding ctx.table) (List.replicate d true)
        (List.replicate ctx.u true) (List.replicate ctx.J true)) := by
  intro i
  rw [FactorServices.clause_frame _ _ _ _ (low_ne i 63 (by decide)) (low_ne i 67 (by decide))]
  exact hlow i

/-- The marked clause is evaluated directly and multiplied once. It does
not pass through the hash idempotent. -/
theorem marked_value_eval_oai (ctx : Context p t n d)
    (minus : RingProgram.Code (Word (baseWidth p t)) d)
    (one seed : Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (incidence : Fin n → Raw (p:=p) (t:=t) (n:=n) (d:=d))
    (entries : List (List Bool × List Bool))
    (hl : ∀ v : Fin n,entries.lookup (Encoding.encodeNat v.val)=some (Product.bytes (incidence v)))
    (ls : List (SAT.Literal (Fin n))) (a : Data)
    (hlow : ∀ i,a.stacks (Clause.callerStacks (Memory.lowPort i))=low ctx i)
    (hsource : a.stacks 63=Encoding.encodeList id (ls.map HashCircuitProgram.Native.Clause.literalBits))
    (htable : a.stacks 62=Squarefree.Program.lookupRecords entries)
    (hone : a.stacks 69=Product.bytes one) (hminus : a.stacks 76=RingProgram.flat minus)
    (hwork : ∀ i ∈ FactorServices.clauseScratch,a.stacks (Clause.callerStacks i)=[])
    (hseed : a.stacks 151=Product.bytes seed) (htmp : a.stacks 159=[]) :
    let factor := FactorServices.clauseResult ctx minus one incidence ls
    let result := Product.run p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor []
    ∃ k b,k  ≤  FactorServices.clauseBudget ctx minus one incidence entries ls+
        (2*(a.stacks 62).length+3+productBudget p t ctx.modulus ctx.cache ctx.table ctx.u ctx.J seed factor) ∧
      Eval (.seq Clause.caller (.seq (clear 62) accumulate)) k a b ∧
      b.stacks=Function.update (Function.update (Function.update
        (Function.update a.stacks 63 []) 67 []) 62 []) 151 (Product.bytes result) := by
  dsimp only
  obtain ⟨ki,ri,hki,hi⟩ := FactorServices.clause_eval ctx minus one incidence entries hl ls a
    hlow hsource htable hone hminus hwork
  let mid := FactorServices.clauseFinished a ri (Product.bytes (FactorServices.clauseResult ctx minus one incidence ls))
  have h61 : a.stacks 61=[] := hwork 61 (by decide)
  have h70 : a.stacks 70=[] := hwork 70 (by decide)
  obtain ⟨kt,b,hkt,ht,hb⟩ := marked_tail_eval p t ctx.modulus ctx.cache ctx.zeroBound ctx.table
    (List.replicate d true) ctx.width (by simp) ctx.widthLength ctx.u ctx.J seed
    (FactorServices.clauseResult ctx minus one incidence ls) mid
    (clause_lowReady ctx a ri _ hlow)
    (by simpa [mid,FactorServices.clauseFinished] using hseed)
    (by simp [mid,FactorServices.clauseFinished])
    (by simpa [mid,FactorServices.clauseFinished] using h61)
    (by simpa [mid,FactorServices.clauseFinished] using h70)
    (by simpa [mid,FactorServices.clauseFinished] using htmp)
  have hm62 : mid.stacks 62=a.stacks 62 := by simp [mid,FactorServices.clauseFinished]
  rw [hm62] at hkt
  refine ⟨ki+kt,b,by omega,hi.seq ht,?_⟩
  rw [hb]
  funext i
  by_cases h63 : i=63 <;> by_cases h67 : i=67 <;> by_cases h62 : i=62 <;> by_cases h151 : i=151 <;>
    simp [mid,FactorServices.clauseFinished,h63,h67,h62,h151]

end SubexponentialSAT.SqrtLog.LeafProgram.Factor

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Factor.marked_value_eval_oai
