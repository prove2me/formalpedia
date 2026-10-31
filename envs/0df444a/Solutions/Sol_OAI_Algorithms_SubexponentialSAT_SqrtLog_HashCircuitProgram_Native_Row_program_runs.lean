-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:46:19.928658+00:00
-- url     : https://prove2.me/submissions/a1f503c6-5159-47a4-9a52-d61a27ec5607

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S139
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_Clause_callback_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_WeightedCallbacks_accumulate_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_HashCircuitProgram_Native_rowFrame_memory

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramRows
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical opening of an inline weighted clause record. The record payload is
`frame coefficient ++ encodeList encodeNat clause`. It is supplied reversed by
the outer record parser. Both the weight frame and the literal list are traversed
by fixed bit programs; source clause IDs are resolved by the upstream producer. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

theorem transfer_eval (regs : Fin 5 → Bool) (payload : List Bool) :
    Eval transfer (3*payload.length+3)
      (recordState regs payload.reverse [] [] [] [] [])
      (recordState (readRegs regs 0 1 none) [] [] payload [] [] []) := by
  let d := recordState regs payload.reverse [] [] [] [] []
  have h := StackRoutines.transferProgram_trace (0 : Fin 6) 2 (0 : Fin 5) 1
    (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  have hs : StackRoutines.transferStacks (0 : Fin 6) 2 d.stacks =
      (recordState (readRegs regs 0 1 none) [] [] payload [] [] []).stacks := by
    funext i; fin_cases i <;> simp [d,StackRoutines.transferStacks]
  apply Eval.call
  simp only [StackRoutines.transferResult] at hh
  rw [hs] at hh
  simpa [d,recordState,storage,StructuredProgram.State.withPC,StackRoutines.transferProgram,
    Nat.add_assoc] using hh

private theorem after_weight (regs : Fin 5 → Bool) (weight clause : List Bool) :
    afterFrame (recordState regs [] [] (Encoding.frame weight ++ clause) [] [] [])
      2 5 weight clause =
        recordState (readRegs regs 0 1 (some false)) [] [] clause [] [] weight.reverse := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i <;> simp []

theorem openWeighted_eval (regs : Fin 5 → Bool) (weight clause : List Bool) :
    Eval openWeighted (3*(Encoding.frame weight ++ clause).length + 6*weight.length+7)
      (recordState regs (Encoding.frame weight ++ clause).reverse [] [] [] [] [])
      (recordState (readRegs (readRegs regs 0 1 none) 0 1 (some false))
        [] [] clause [] [] weight.reverse) := by
  have ht := transfer_eval regs (Encoding.frame weight ++ clause)
  have hp := parseFrame_eval (recordState (readRegs regs 0 1 none)
    [] [] (Encoding.frame weight ++ clause) [] [] []) 2 5 (by decide) weight clause rfl
  rw [after_weight] at hp
  convert ht.seq hp using 1 ; omega

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Rows

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed caller framing for the native sparse-hash interpreter. Low ports
0--55 are reserved for arithmetic. Literal lookup uses 56--62, leaving the
clause, row and constant accumulators physically untouched. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem rowRegisters_injective : Function.Injective rowRegisters := Fin.castAdd_injective _ _
theorem rowStacks_injective : Function.Injective rowStacks := by decide

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

end OAI.Algorithms
end

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

theorem clear_eval (d : Machine) (src : Fin 96) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared d src) := by
  apply Eval.call
  have h := StackRoutines.clearProgram_trace src (0 : Fin 8) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 2 rfl rfl
  simpa [cleared,StackRoutines.clearResult,StructuredProgram.State.withPC,
    StackRoutines.clearProgram,Nat.add_assoc] using hh

theorem recordReturn_eval (d : Machine) : Eval recordReturn 3 d (returned d) := by
  exact (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 8) false) d)).seq
    ((Eval.base (StructuredProgram.Eval.atom (.set (1 : Fin 8) true) _)).seq
      (Eval.base (StructuredProgram.Eval.atom (.set (2 : Fin 8) false) _)))

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

theorem clear_high (regs : Fin 8 → Bool) (low : Fin 56 → List Bool) (high : Fin 40 → List Bool)
    (src : Fin 40) :
    Eval (clear (highPort src)) (2*(high src).length+3) (state regs low high)
      (state (readRegs regs 0 1 none) low (Function.update high src [])) := by
  simpa only [state,cleared,StackRoutines.clearStacks,tapes_high,update_high] using
    Native.clear_eval (state regs low high) (highPort src)

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Memory

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeIndexEncoding
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A self-delimiting encoding of sparse keys: two unary numeric fields,
followed by exactly n support bits. The encoding works without precision
assumptions; the precision assumptions only bound its length. -/

namespace SubexponentialSAT.SqrtLog.Squarefree

theorem encodeMask_injective {n : ℕ} :
    Function.Injective (encodeMask (n := n)) := by
  intro a b h
  have hf : (fun i : Fin n => decide (i ∈ a)) =
      (fun i : Fin n => decide (i ∈ b)) := List.ofFn_injective h
  ext i
  have hi := congrFun hf i
  by_cases ha : i ∈ a <;> by_cases hb : i ∈ b <;> simp_all

theorem encodeIndex_injective {n : ℕ} :
    Function.Injective (encodeIndex (n := n)) := by
  intro a b h
  have hfirst : a.u = b.u ∧
      Encoding.encodeNat a.z ++ encodeMask a.vars =
        Encoding.encodeNat b.z ++ encodeMask b.vars := by
    simpa [encodeIndex, List.append_assoc] using congrArg Encoding.readNat h
  have hsecond : a.z = b.z ∧ encodeMask a.vars = encodeMask b.vars := by
    simpa using congrArg Encoding.readNat hfirst.2
  have hs := encodeMask_injective hsecond.2
  cases a
  cases b
  cases hfirst.1
  cases hsecond.1
  cases hs
  rfl

end SubexponentialSAT.SqrtLog.Squarefree

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HashCircuitProgramRowMemory
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact frame for unpacking an inline weighted clause into the two physical
operands used by the clause loop and weighted accumulator. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem project_weighted (d : Machine) (payload : List Bool)
    (h : WeightedReady d) (hp : d.stacks 66 = payload) :
    projectState rowRegisters rowStacks d =
      SubexponentialSAT.SubexpRecordScan.recordState (rowCallerRegs d) payload [] [] [] [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i; fin_cases i
    · exact hp
    · exact h.temporary
    · exact h.clause
    · exact h.compare
    · exact h.scratch
    · exact h.weight

theorem openWeighted_from_state (d : Machine) (weight clause : List Bool)
    (h : WeightedReady d) (hp : d.stacks 66 = (Encoding.frame weight ++ clause).reverse) :
    let rr := readRegs (readRegs (rowCallerRegs d) 0 1 none) 0 1 (some false)
    Eval openWeighted (3*(Encoding.frame weight ++ clause).length+6*weight.length+8)
      d (rowFrame d rr [] clause weight.reverse) := by
  dsimp only
  have he := Rows.openWeighted_eval (rowCallerRegs d) weight clause
  rw [← project_weighted d _ h hp] at he
  have hh := eval_liftCommand_from_state Rows.openWeighted 0 2 rowRegisters rowStacks d
    rowRegisters_injective rowStacks_injective he
  simpa only [Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native

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
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

theorem record_state (regs : Fin 8 → Bool) (e : Product.Store) (high : Fin 40 → List Bool)
    (acc src payload : List Bool) (v pr f : Bool) :
    RecordPrograms.state rowPorts (base regs e high acc) v pr f src payload =
      Memory.state (Function.update (Function.update (Function.update regs 0 v) 1 pr) 2 f)
        (Product.tapes e) (recordHigh high acc src payload) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · change Function.update (Function.update (Memory.tapes (Product.tapes e) (baseHigh high acc))
      (Memory.highPort 8) src) (Memory.highPort 10) payload =
      Memory.tapes (Product.tapes e) (recordHigh high acc src payload)
    rw [Memory.update_high,Memory.update_high]
    rfl

private theorem accumulated_recordHigh
    (high : Fin 40 → List Bool) (acc tail payload literals scalar one clause result : List Bool) :
    WeightedCallbacks.accumulatedHigh
        (Clause.recordHigh
          (Function.update (openedHigh (recordHigh high acc tail payload) literals scalar) 11 one)
          clause [] []) result =
      recordHigh high result tail [] := by
  funext i
  fin_cases i <;>
    simp [WeightedCallbacks.accumulatedHigh, Clause.recordHigh, Clause.baseHigh,
      literalHigh, openedHigh, recordHigh, baseHigh]

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

theorem callback_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (w : WeightedClause n (baseWidth p t) d) (acc : List (Product.Entry n (baseWidth p t) d)) (tail : List Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    ∃ k ≤ cost p t M cache table minusOne one incidence degree u J entries w acc,
      ∃ rr, Eval (weightedClauseStep arithmetic) k
        (RecordPrograms.state rowPorts (base regs e high (Product.bytes acc))
          false true false tail (payload w).reverse)
        (RecordPrograms.state rowPorts
          (base rr e high (Product.bytes (value p t M cache table minusOne one incidence u J w acc)))
          false true false tail []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let r0 := Function.update (Function.update (Function.update regs 0 false) 1 true) 2 false
  let h0 := recordHigh high (Product.bytes acc) tail (payload w).reverse
  let start := Memory.state r0 (Product.tapes e) h0
  have hready : WeightedReady start := by
    constructor <;> simp [start,Memory.state,Memory.tapes,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh]
  have hp : start.stacks 66 = (Encoding.frame (RingProgram.flat w.scalar) ++ literalList w).reverse := by
    simp [start,Memory.state,Memory.tapes,h0,recordHigh,payload]
  have hopen := openWeighted_from_state start (RingProgram.flat w.scalar) (literalList w) hready hp
  let openRegs := readRegs (readRegs (rowCallerRegs start) 0 1 none) 0 1 (some false)
  let opened := rowFrame start openRegs [] (literalList w) (RingProgram.flat w.scalar).reverse
  let h1 := openedHigh h0 (literalList w) (RingProgram.flat w.scalar).reverse
  have hopenMemory : opened = Memory.state opened.regs (Product.tapes e) h1 :=
    rowFrame_memory r0 (Product.tapes e) h0 openRegs (literalList w) (RingProgram.flat w.scalar).reverse
  change Eval openWeighted (3*(payload w).length+6*(RingProgram.flat w.scalar).length+8) start opened at hopen
  rw [hopenMemory] at hopen
  have htmp1 : h1 14 = [] := by simpa [h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh] using htmp
  have hcopy := Memory.copy_high_high opened.regs (Product.tapes e) h1 13 11 14
    (by decide) (by decide) (by decide) htmp1
  have hone1 : h1 13 = Product.bytes one := by simpa [h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh] using ho
  have hacc1 : h1 11 = [] := by simp [h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh]
  simp only [hone1,hacc1,List.append_nil] at hcopy
  let r1 := readRegs opened.regs 0 1 none
  let h2 := Function.update h1 (11 : Fin 40) (Product.bytes one)
  obtain ⟨kc,hkc,rc,hclause⟩ := Clause.command_eval p t M cache table minusOne one incidence degree u J entries hz
    width hd hw hl r1 h2
    (by simpa [h2,h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh] using ht)
    (by simpa [h2] using hone1)
    (by simpa [h2,h1,openedHigh,h0,recordHigh,baseHigh,Clause.baseHigh,literalHigh] using hm)
    (by simpa [h2] using htmp1)
    w.literals one [] (r1 0) (r1 1) (r1 2)
  let clause := clauseValue p t M cache table minusOne one incidence u J w
  let h3 := Clause.recordHigh h2 (Product.bytes clause) [] []
  let r2 := Function.update (Function.update (Function.update rc 0 false) 1 true) 2 false
  have hclauseStart : RecordPrograms.state literalPorts (Clause.base r1 e h2 (Product.bytes one))
      (r1 0) (r1 1) (r1 2) (Encoding.encodeList id (w.literals.map Clause.literalBits) ++ []) [] =
      Memory.state r1 (Product.tapes e) h2 := by
    rw [Clause.record_state]
    apply congrArg₂ StructuredProgram.State.mk
    · simp
    · apply congrArg (Memory.tapes (Product.tapes e))
      funext i; fin_cases i <;> simp [Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh,h0,recordHigh,baseHigh,literalList]
  rw [hclauseStart,Clause.record_state] at hclause
  change Eval (clauseLoop arithmetic) kc (Memory.state r1 (Product.tapes e) h2)
    (Memory.state r2 (Product.tapes e) h3) at hclause
  obtain ⟨ka,hka,ra,hacc⟩ := WeightedCallbacks.accumulate_eval p t M cache hz table w.scalar degree width
    (List.replicate u true) (List.replicate J true) hd hw Squarefree.encodeIndex Squarefree.encodeIndex_injective
    clause acc r2 h3
    (by simp [h3,Clause.recordHigh,Clause.baseHigh,Product.bytes,Normalize.bytes,Squarefree.ScaleProgram.encode])
    (by simp [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh])
    (by simp [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh,h0,recordHigh,baseHigh])
    (by simpa [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2] using htmp1)
  let result := value p t M cache table minusOne one incidence u J w acc
  let h4 := recordHigh high (Product.bytes result) tail []
  have hfinish : WeightedCallbacks.accumulatedHigh h3 (Product.bytes result) = h4 := by
    simpa [h3,h4,h2,h1,h0] using accumulated_recordHigh high (Product.bytes acc)
      tail (payload w).reverse (literalList w) (RingProgram.flat w.scalar).reverse
      (Product.bytes one) (Product.bytes clause) (Product.bytes result)
  change Eval accumulate ka (Memory.state r2 (Product.tapes e) h3)
    (Memory.state ra (Product.tapes e) (WeightedCallbacks.accumulatedHigh h3 (Product.bytes result))) at hacc
  rw [hfinish] at hacc
  have hreturn := recordReturn_eval (Memory.state ra (Product.tapes e) h4)
  refine ⟨(3*(payload w).length+6*(RingProgram.flat w.scalar).length+8)+(7*(Product.bytes one).length+5)+kc+ka+3,?_,ra,?_⟩
  · dsimp only [cost]
    have h11 : h3 11 = Product.bytes clause := by simp [h3,Clause.recordHigh,Clause.baseHigh]
    have h9 : h3 9 = (RingProgram.flat w.scalar).reverse := by simp [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh]
    have h12 : h3 12 = Product.bytes acc := by simp [h3,Clause.recordHigh,Clause.baseHigh,literalHigh,h2,h1,openedHigh,h0,recordHigh,baseHigh]
    rw [h11,h9,h12,List.length_reverse] at hka
    dsimp only [clause,result,clauseValue,value,Product.bytes] at hka hkc ⊢
    omega
  · rw [record_state,record_state]
    convert hopen.seq (hcopy.seq (hclause.seq (hacc.seq hreturn))) using 1 <;> first | rfl | omega

/-- Every weighted clause is read from the supplied row and executed once. -/
theorem loop_eval (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (ws : List (WeightedClause n (baseWidth p t) d)) (acc : List (Product.Entry n (baseWidth p t) d))
    (suffix : List Bool) (v pr f : Bool) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    let update := value p t M cache table minusOne one incidence u J
    ∃ k ≤ 3+DynamicFold.work payload update (cost p t M cache table minusOne one incidence degree u J entries) ws acc,
      ∃ rr, Eval (rowLoop arithmetic) k
        (RecordPrograms.state rowPorts (base regs e high (Product.bytes acc)) v pr f
          (Encoding.encodeList id (ws.map payload) ++ suffix) [])
        (RecordPrograms.state rowPorts
          (base rr e high (Product.bytes (DynamicFold.value update ws acc))) false true false suffix []) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let update := value p t M cache table minusOne one incidence u J
  let charge := cost p t M cache table minusOne one incidence degree u J entries
  let Rep : List (Product.Entry n (baseWidth p t) d) → Machine → Prop :=
    fun a b => ∃ rr, b = base rr e high (Product.bytes a)
  have hc : DynamicFold.Contract rowPorts (weightedClauseStep arithmetic) payload update charge Rep := by
    intro w a b hb tail
    obtain ⟨rflRegs,rfl⟩ := hb
    obtain ⟨k,hk,rr,he⟩ := callback_eval p t M cache table minusOne one incidence degree u J entries
      hz width hd hw hl rflRegs high ht ho hm htmp w a tail
    exact ⟨k,base rr e high (Product.bytes (update w a)),hk,⟨rr,rfl⟩,he⟩
  obtain ⟨k,next,hk,hn,he⟩ := DynamicFold.command_eval rowPorts (weightedClauseStep arithmetic) payload
    update charge Rep hc ws acc (base regs e high (Product.bytes acc)) ⟨regs,rfl⟩ suffix v pr f
  obtain ⟨rr,rfl⟩ := hn
  exact ⟨k,hk,rr,he⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

/-! Component: HashCircuitProgramRun. All public namespaces and APIs are retained. -/


/-! Compiled fixed-program trace for one serialized sparse hash row. The
initial accumulator is physically cleared, and the final halt is charged. -/
namespace SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open MomentsProgram

variable (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
variable (cache : RingProgram.ScalarCache p t) {n d : ℕ}
variable (table : Fin d → Fin d → Fin d → Word (baseWidth p t))
variable (minusOne : RingProgram.Code (Word (baseWidth p t)) d)
variable (one : List (Product.Entry n (baseWidth p t) d))
variable (incidence : Fin n → List (Product.Entry n (baseWidth p t) d))
variable (degree : List Bool) (u J : ℕ) (entries : List (List Bool × List Bool))

theorem program_runs_oai (hz : BinaryArithmetic.toNat cache.zero.val < p^t)
    (width : List Bool) (hd : degree.length = d) (hw : width.length = baseWidth p t)
    (hl : ∀ v : Fin n, entries.lookup (Encoding.encodeNat v.val) = some (Product.bytes (incidence v)))
    (regs : Fin 8 → Bool) (high : Fin 40 → List Bool)
    (ht : high 6 = Squarefree.Program.lookupRecords entries)
    (ho : high 13 = Product.bytes one) (hm : high 20 = RingProgram.flat minusOne) (htmp : high 14 = [])
    (ws : List (WeightedClause n (baseWidth p t) d)) :
    let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
      (List.replicate u true) (List.replicate J true)
    let update := value p t M cache table minusOne one incidence u J
    let input := Encoding.encodeList id (ws.map payload)
    ∃ rr, RunsIn Native.program
      (7+DynamicFold.work payload update (cost p t M cache table minusOne one incidence degree u J entries) ws [])
      ((RecordPrograms.state rowPorts (base regs e high []) false true false input []).withPC
        (some Native.program.entry))
      ((RecordPrograms.state rowPorts
        (base rr e high (Product.bytes (DynamicFold.value update ws []))) false true false [] []).withPC none) := by
  dsimp only
  let e := Product.idle M.bits width cache.zero.val (RingTriple.tableEncoding table) degree
    (List.replicate u true) (List.replicate J true)
  let input := Encoding.encodeList id (ws.map payload)
  let r0 := Function.update (Function.update (Function.update regs 0 false) 1 true) 2 false
  let r1 := readRegs r0 0 1 none
  let h0 := recordHigh high [] input []
  have hzero : h0 12 = [] := by simp [h0,recordHigh,baseHigh]
  have hsame : Function.update h0 (12 : Fin 40) [] = h0 := by
    rw [← hzero]
    exact Function.update_eq_self 12 h0
  have clearRun := Memory.clear_high r0 (Product.tapes e) h0 12
  simp only [hzero,hsame] at clearRun
  have hclear : Eval (clear 68) 3
      (RecordPrograms.state rowPorts (base regs e high []) false true false input [])
      (RecordPrograms.state rowPorts (base r1 e high []) (r1 0) (r1 1) (r1 2) input []) := by
    rw [record_state,record_state]
    rw [show Memory.highPort 12 = (68 : Fin 96) by decide] at clearRun
    simpa only [r0,r1,h0,List.length_nil,Nat.mul_zero,zero_add,
      Function.update_eq_self] using clearRun
  obtain ⟨k,hk,rr,he⟩ := loop_eval p t M cache table minusOne one incidence degree u J entries hz
    width hd hw hl r1 high ht ho hm htmp ws [] [] (r1 0) (r1 1) (r1 2)
  simp only [List.append_nil] at he
  have hrun : Eval Native.command (3+k)
      (RecordPrograms.state rowPorts (base regs e high []) false true false input [])
      (RecordPrograms.state rowPorts
        (base rr e high (Product.bytes (DynamicFold.value
          (value p t M cache table minusOne one incidence u J) ws []))) false true false [] []) :=
    hclear.seq he
  exact ⟨rr,3+k+1,by omega,compiled_halt_trace hrun 64 68⟩

end SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HashCircuitProgram.Native.Row.program_runs_oai
