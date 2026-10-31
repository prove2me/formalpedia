-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:57:40.36966+00:00
-- url     : https://prove2.me/submissions/18131bf7-c745-462c-82f6-9e39d87e52b1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_duplicate_step
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_exhausted_successor_step
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_fresh_internal_step
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_scan_kernel
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_scanner_caps_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_fresh_leaf_run_space
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement_probe_endpoint_bound
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

open BitProgram

theorem readRegs_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (top : Option Bool) (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present top j = regs j := by
  simp [readRegs, hv, hp]

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# First occurrences of attained keys

The subtype below is a specification of emissions, not a stored family.
The executable scan checks a candidate against its predecessors one at a time.
The key may be an entire integer row-signature; no coordinate projection occurs.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures

variable {N : ℕ} {κ : Type*} (key : Fin N → κ)

theorem duplicateScan_eq_true_iff [DecidableEq κ] (key : ℕ → κ) (candidate bound : ℕ) :
    duplicateScan key candidate bound = true ↔ ∃ j < bound, key j = key candidate := by
  induction bound with
  | zero => simp [duplicateScan]
  | succ bound ih =>
    simp only [duplicateScan, Bool.or_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro (⟨j, hj, he⟩ | he)
      · exact ⟨j, Nat.lt_succ_of_lt hj, he⟩
      · exact ⟨bound, Nat.lt_succ_self _, he⟩
    · rintro ⟨j, hj, he⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hj | rfl
      · exact Or.inl ⟨j, hj, he⟩
      · exact Or.inr he

theorem duplicateScan_eq_false_iff [DecidableEq κ] (key : ℕ → κ) (candidate bound : ℕ) :
    duplicateScan key candidate bound = false ↔ ∀ j < bound, key j ≠ key candidate := by
  rw [← Bool.not_eq_true, duplicateScan_eq_true_iff]
  simp

theorem rescan_emits_iff [DecidableEq κ] (key : ℕ → κ) (i : Fin N) :
    duplicateScan key i i = false ↔ ∀ j : Fin N, j < i → key j ≠ key i := by
  rw [duplicateScan_eq_false_iff]
  constructor
  · intro h j hj
    exact h j hj
  · intro h j hj
    exact h ⟨j, hj.trans i.isLt⟩ hj

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

theorem Iteration.eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (h : Iteration p q n a b) : Eval (body p q) n a b := by
  cases h with
  | leaf hl hv ha => exact .ite_true hl (.seq hv ha)
  | fresh hl hp hb hf hd =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_true hb (Eval.ite_true hf hd)))
  | duplicate hl hp hb hf hn =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_true hb (Eval.ite_false hf hn)))
  | exhausted hl hp hb ha =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_false hb ha))

theorem suspendedFrames_length_le (frames : List (List Bool)) (width levels : ℕ)
    (hdepth : frames.length ≤ levels)
    (hwidth : ∀ frame ∈ frames, frame.length ≤ width) :
    (suspendedFrames frames).length ≤ (2 * width + 1) * levels := by
  have h : (suspendedFrames frames).length ≤ (2 * width + 1) * frames.length := by
    induction frames with
    | nil => simp [suspendedFrames]
    | cons frame frames ih =>
        have hf := hwidth frame (by simp)
        have hh := ih (by simp only [List.length_cons] at hdepth; omega)
          (fun word hw => hwidth word (by simp [hw]))
        simp only [suspendedFrames, List.flatMap_cons, List.length_append,
          Encoding.length_frame, List.length_reverse, List.length_cons,
          Nat.mul_add, Nat.mul_one] at *
        omega
  exact h.trans (Nat.mul_le_mul_left _ hdepth)

theorem pushWordState_src (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    (pushWordState src dst h a).stacks src = [] :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 0

theorem pushWordState_dst (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896) :
    (pushWordState src dst h a).stacks dst =
      Encoding.frame (a.stacks src).reverse ++ a.stacks dst :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 1

theorem pushWordState_outside (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (pushWordState src dst h a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

theorem saveCursorState_words (a : State 40 896) :
    (saveCursorState a).stacks (tupleStacks 2) = [] ∧
      (saveCursorState a).stacks (tupleStacks 7) = [] ∧
      (saveCursorState a).stacks (tupleStacks 0) =
        Encoding.frame (a.stacks (tupleStacks 7)).reverse ++
          Encoding.frame (a.stacks (tupleStacks 2)).reverse ++ a.stacks (tupleStacks 0) := by
  constructor
  · unfold saveCursorState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide), pushWordState_src]
  constructor
  · exact pushWordState_src _ _ _ _
  · unfold saveCursorState
    rw [pushWordState_dst, pushWordState_dst,
      pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    exact List.append_assoc _ _ _ |>.symm

theorem recordRepresentativeState_words (a : State 40 896)
    (hp : a.stacks (tupleStacks 4) = []) :
    (recordRepresentativeState a).stacks (tupleStacks 1) =
        Encoding.frame (a.stacks (tupleStacks 2)).reverse ++ a.stacks (tupleStacks 1) ∧
      (recordRepresentativeState a).stacks (tupleStacks 2) = a.stacks (tupleStacks 2) ∧
      (recordRepresentativeState a).stacks (tupleStacks 4) = [] := by
  constructor
  · unfold recordRepresentativeState
    rw [pushWordState_dst]
    simp [copyState, StackRoutines.copyStacks, hp]
  constructor
  · unfold recordRepresentativeState
    rw [pushWordState_outside _ _ _ _ _ (by decide) (by decide)]
    simp [copyState, StackRoutines.copyStacks]
  · exact pushWordState_src _ _ _ _

theorem descendLevelState_words (a : State 40 896) (remaining address : ℕ)
    (hr : a.stacks (tupleStacks 6) = List.replicate (remaining + 1) true)
    (ha : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendLevelState a).stacks (tupleStacks 6) = List.replicate remaining true ∧
      (descendLevelState a).stacks (tupleStacks 9) = List.replicate (address + 1) true ∧
      (descendLevelState a).regs controllerPorts.leaf = decide (remaining = 0) := by
  have h69 : tupleStacks 6 ≠ tupleStacks 9 := by decide
  cases remaining <;>
    simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      hr, ha, List.replicate_succ, controllerPorts, h69, Ne.symm h69]

theorem clearWord_eval (src : Fin 896) (a : State 40 896) :
    Eval (clearWord src) (2 * (a.stacks src).length + 3) a (clearState src a) := by
  have ht := StackRoutines.clearProgram_trace src (0 : Fin 40) 1 a.regs a.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  exact .call _ (by simpa [clearState, StackRoutines.clearResult, StackRoutines.clearStacks,
    StructuredProgram.State.withPC, StackRoutines.clearProgram, Nat.add_assoc] using hh)

theorem clearWords_eval (ports : List (Fin 896)) (a : State 40 896) :
    Eval (clearWords ports) (clearWordsTime ports a) a (clearWordsState ports a) := by
  induction ports generalizing a with
  | nil => exact .base (.skip _)
  | cons src rest ih => exact .seq (clearWord_eval src a) (ih _)

theorem clearWordsState_stacks (ports : List (Fin 896)) (a : State 40 896)
    (i : Fin 896) :
    (clearWordsState ports a).stacks i = if i ∈ ports then [] else a.stacks i := by
  induction ports generalizing a with
  | nil => simp [clearWordsState]
  | cons src rest ih =>
    rw [clearWordsState, ih]
    by_cases hr : i ∈ rest
    · simp [hr]
    · by_cases hi : i = src
      · subst i
        simp [hr, clearState]
      · simp [hr, hi, clearState]

theorem testParent_eval (a : State 40 896) :
    Eval testParentCommand 1 a (testParentState a) := .base (.atom _ _)

theorem testParentState_flag (a : State 40 896) :
    (testParentState a).regs controllerPorts.active =
      decide (a.stacks (tupleStacks 0) ≠ []) := by
  cases hs : a.stacks (tupleStacks 0) <;>
    simp [testParentState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs, hs]

theorem testAvailable_eval (a : State 40 896) (hs : a.stacks remainingPorts.scratch = []) :
    Eval testAvailableCommand (8 * (a.stacks remainingPorts.counter).length + 8) a
      (testAvailableState a) := by
  have ht := Eval.seq (CounterForPrograms.test_eval remainingPorts a hs)
    (Eval.base (StructuredProgram.Eval.atom
      (.copy controllerPorts.available (remainingPorts.register 2)) _))
  simpa only [testAvailableCommand, testAvailableState, Nat.add_assoc] using ht

theorem testAvailableState_flag (a : State 40 896) :
    (testAvailableState a).regs controllerPorts.available =
      !(CounterPrograms.isZero (a.stacks remainingPorts.counter)) :=
  CounterForPrograms.testResult_flag remainingPorts a

/-- Generic frame operations preserve every controller flag. -/
theorem pushWordState_register_frame (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (pushWordState src dst h a).regs i = a.regs i := by
  apply embedState_register_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact h0 hj.symm
  · exact h1 hj.symm

theorem clearWordsState_register_frame (ports : List (Fin 896))
    (a : State 40 896) (i : Fin 40) (h0 : i ≠ 0) (h1 : i ≠ 1) :
    (clearWordsState ports a).regs i = a.regs i := by
  induction ports generalizing a with
  | nil => rfl
  | cons src rest ih =>
    rw [clearWordsState, ih]
    exact StackRoutines.readRegs_frame a.regs 0 1 i none h0 h1

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

namespace QueryReady

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a) (hf : QueryMasterFrame a b) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf.word 128 (by decide)).trans h.ambient
    theta := (hf.word 78 (by decide)).trans h.theta
    modulus := (hf.word 194 (by decide)).trans h.modulus
    table := (hf.word 201 (by decide)).trans h.table
    width := (hf.word 202 (by decide)).trans h.width
    scalarZero := (hf.word 203 (by decide)).trans h.scalarZero
    degree := (hf.word 204 (by decide)).trans h.degree
    one := (hf.word 207 (by decide)).trans h.one
    minus := (hf.word 211 (by decide)).trans h.minus
    precision := (hf.word 212 (by decide)).trans h.precision
    order := (hf.word 243 (by decide)).trans h.order
    zero := (hf.word 280 (by decide)).trans h.zero
    code := (hf.word 281 (by decide)).trans h.code
    clauses := (hf.word 700 (by decide)).trans h.clauses
    rows := (hf.word 701 (by decide)).trans h.rows
    rowCount := (hf.word 704 (by decide)).trans h.rowCount
    markedIndex := (hf.word 705 (by decide)).trans h.markedIndex
    markedFlag := (hf.word 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf.word 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf.word 708 (by decide))).trans h.indexWidth
    highMask := (hf.word 702 (by decide)).trans h.highMask
    highBits := (hf.word 703 (by decide)).trans h.highBits
    outer := (hf.word 858 (by decide)).trans h.outer
    inner := (hf.word 857 (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf.word 130 (by decide)).trans h.colors
    nodes := (hf.word 131 (by decide)).trans h.nodes
    typeWidth := (hf.word 132 (by decide)).trans h.typeWidth
    positive := (hf.word 710 (by decide)).trans h.positive
    negative := (hf.word 711 (by decide)).trans h.negative
    sourceWidth := (hf.word 140 (by decide)).trans h.sourceWidth
    power := (hf.word 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf.word 138 (by decide)).trans h.radius
    offset := (hf.word 139 (by decide)).trans h.offset
    metadata := (hf.word 135 (by decide)).trans h.metadata
    plans := (hf.word 136 (by decide)).trans h.plans
    inverses := (hf.word 713 (by decide)).trans h.inverses
    negatives := (hf.word 714 (by decide)).trans h.negatives
    differences := (hf.word 715 (by decide)).trans h.differences
    ringWidth := (hf.word 717 (by decide)).trans h.ringWidth
    rowWidth := (hf.word 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf.word 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈masterPorts := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf.word _ hm]
    exact h.cacheCaps p hp
  · rw [hf.word 128 (by decide)]
    exact h.ambientCap
  · rw [hf.word 207 (by decide)]
    exact h.oneCap

end QueryReady

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end PairAccumulatorMeaning

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessRow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A measured signed row scan, followed by a physical frame-order repair. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedWords_length {W : List Bool} {xs : List SignedWord} {ys : List (List Bool)}
    (h : List.Forall₂ (shiftedWord W) xs ys) : xs.length=ys.length := by
  induction h with
  | nil => rfl
  | cons h hs ih => simpa using ih

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_BucketProgramPreprocessBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Integer semantics and explicit polynomial bounds for the concrete
signed-coefficient preprocessing machine. -/
namespace SubexponentialSAT.SqrtLog.BucketProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.MatrixProgramSupport

theorem shiftedMatrix_rowWidth {W : List Bool} {xs : List (List SignedWord)}
    {ys : List (List (List Bool))} (h : List.Forall₂ (List.Forall₂ (shiftedWord W)) xs ys)
    (width : ℕ) (hw : ∀ row∈xs, row.length=width) :
    ∀ row∈ys, row.length=width := by
  induction h with
  | nil => simp
  | @cons a y xs ys hy hys ih =>
      intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact (shiftedWords_length hy).symm.trans (hw a (by simp))
      · exact ih (fun a ha => hw a (by simp [ha])) z hz

end SubexponentialSAT.SqrtLog.BucketProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutMatrixProgramCompatibility
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact serialization and state projection at the all-row bucket boundary. -/
namespace SubexponentialSAT.SqrtLog.LayoutMatrixProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem matrixRel_dimensions {Rel : ℕ → ℕ → Pair → Prop} {B D : ℕ} {js : List ℕ}
    {rows : List (List Pair)} (h : MatrixRel Rel B D js rows) :
    rows.length=D ∧ ∀ row ∈ rows, row.length=js.length := by
  refine ⟨?_,?_⟩
  · simpa [MatrixRel] using h.length_eq.symm
  · intro row hr
    have aux : ∀ (is : List ℕ) (rs : List (List Pair)),
        List.Forall₂ (fun j row => List.Forall₂ (fun v p => Rel j v p ∧ pairLength p ≤ B) js row)
          is rs → ∀ row ∈ rs, row.length=js.length := by
      intro is rs hs
      induction hs with
      | nil => simp
      | cons hi ht ih =>
        intro row hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hi.length_eq.symm
        · exact ih row hr
    exact aux _ _ h row hr

end SubexponentialSAT.SqrtLog.LayoutMatrixProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem count_le (p : ℕ → Bool) (n : ℕ) : count p n ≤ n := by
  simpa [count,chosenIds] using List.length_filter_le p (List.range n)

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBoundsPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed polynomial cost of actual head-ID, support-mask, and factor-ID
preparation. Bounds include the real isolated-bank copy/cleanup costs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

 theorem selectedHeads_length (n : ℕ) (rows : List (List Bool)) (low : List Bool) (z : ℕ) :
    (selectedHeads n rows low z).length ≤ n :=
  HeadIdentifierProgram.count_le _ _

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Bounds

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoaderCore
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed head-loader table uses the actual integer entry program. Its
physical matrix view follows LeafHeadSetupProgramHead/MatrixRun exactly, while
its controller emits one matrix and never constructs assignment tables. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- The physical shifted rows retain every incidence and the exact emitted
column order, including empty matrices and empty heads. -/
theorem shiftedMatrix_typed (W : List Bool)
    (Rel : ℕ → ℕ → LayoutMatrixProgram.Pair → Prop) (B D : ℕ)
    (js : List ℕ) (raw : List (List LayoutMatrixProgram.Pair))
    (ys : List (List (List Bool)))
    (hr : LayoutMatrixProgram.MatrixRel Rel B D js raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw ys) :
    ∃ c : Fin D → Fin js.length → List Bool,
      ys = List.ofFn (fun j => List.ofFn (c j)) ∧
      ∀ j i, ∃ p, Rel j.val (js.get i) p ∧
        LayoutMatrixProgram.pairLength p ≤ B ∧ BucketProgram.shiftedWord W p (c j i) := by
  obtain ⟨hlen, hrow⟩ := LayoutMatrixProgram.matrixRel_dimensions hr
  have hylen : ys.length = D := hy.length_eq.symm.trans hlen
  have hyrow : ∀ row ∈ ys, row.length = js.length :=
    BucketProgram.shiftedMatrix_rowWidth hy js.length hrow
  let rowAt (j : Fin D) : List (List Bool) := ys.get ⟨j.val, by omega⟩
  have hrowAt (j : Fin D) : (rowAt j).length = js.length :=
    hyrow _ (List.get_mem _ _)
  let c (j : Fin D) (i : Fin js.length) : List Bool :=
    (rowAt j).get ⟨i.val, by rw [hrowAt]; exact i.isLt⟩
  refine ⟨c, ?_, ?_⟩
  · apply List.ext_get
    · simp [hylen]
    · intro j hj hj'
      simp only [List.get_eq_getElem, List.getElem_ofFn]
      apply List.ext_get
      · simp [← hrowAt ⟨j, by simpa using hj'⟩, rowAt]
      · intro i hi hi'
        simp only [List.get_eq_getElem, List.getElem_ofFn]
        rfl
  · intro j i
    have hjraw : j.val < raw.length := by omega
    have hjrange : j.val < (List.range D).length := by simp
    have hrawrow := hr.get hjrange hjraw
    simp only [List.get_eq_getElem, List.getElem_range] at hrawrow
    have hshiftrow := hy.get hjraw (by omega)
    have hiraw : i.val < (raw.get ⟨j.val,hjraw⟩).length := by
      change i.val < (raw[j.val]'hjraw).length
      rw [← hrawrow.length_eq]
      exact i.isLt
    have hiy : i.val < (ys.get ⟨j.val,by omega⟩).length := by
      exact (hrowAt j).symm ▸ i.isLt
    have hp := hrawrow.get i.isLt hiraw
    have hs := hshiftrow.get hiraw hiy
    exact ⟨_, hp.1, hp.2, hs⟩


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleTraversal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Cursor semantics for the attained-signature tuple controller

The cursor stores an attained prefix and one numeric candidate. Suspended
ancestors are first occurrences, so the tree branches over attained keys only.
The traces and finite sums below are mathematical specifications; the actual
controller retains neither a trace nor a family of assignments or tuples.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal

open scoped BigOperators
open SignatureTupleDFS

open Classical

variable {N : ℕ → ℕ} {κ : ℕ → Type*}

section Frames

open ExecCNFTupleEnumeration SignatureTupleProgram

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem representativeWords_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    representativeWords h key (depth + 1) (Fin.snoc ancestors rep) =
      representativeWords h key depth ancestors ++ [fixedBits (h depth) rep.val.val] := by
  simp only [representativeWords, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append]
  rfl

theorem representativeFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    representativeFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      Encoding.frame (fixedBits (h depth) rep.val.val).reverse ++
        representativeFrames h key depth ancestors := by
  simp [representativeFrames, representativeWords_snoc, suspendedFrames, List.reverse_append]

theorem cursorFrames_snoc (depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth) :
    cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) =
      cursorFrame (h depth) rep.val.val ++ cursorFrames h key depth ancestors := by
  simp only [cursorFrames, List.ofFn_succ', Fin.snoc_castSucc,
    Fin.snoc_last, Fin.val_last, List.concat_eq_append,
    List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatten_cons]
  rfl

theorem representativeFrames_length_le (depth hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hh : ∀ d < depth, h d ≤ hmax) :
    (representativeFrames h key depth ancestors).length ≤ (2 * hmax + 1) * depth := by
  apply suspendedFrames_length_le _ hmax depth
  · simp [representativeWords]
  · intro word hw
    rw [List.mem_reverse, representativeWords, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ := hw
    simpa using hh i.val i.isLt

private theorem flatten_length_le (words : List (List Bool)) (bound : ℕ)
    (hw : ∀ word ∈ words, word.length ≤ bound) : words.flatten.length ≤ words.length * bound := by
  induction words with
  | nil => simp
  | cons word words ih =>
      have hword := hw word (by simp)
      have htail := ih (fun w hmem => hw w (by simp [hmem]))
      simp only [List.flatten_cons, List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

theorem cursorFrame_length (width candidate : ℕ) :
    (cursorFrame width candidate).length = 4 * width + 4 := by
  simp [cursorFrame]
  omega

theorem cursorFrames_length_le (depth hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hh : ∀ d < depth, h d ≤ hmax) :
    (cursorFrames h key depth ancestors).length ≤ (4 * hmax + 4) * depth := by
  unfold cursorFrames
  have hb := flatten_length_le
    (List.ofFn fun i : Fin depth => cursorFrame (h i.val) (ancestors i).val.val).reverse
    (4 * hmax + 4) (by
      intro word hw
      rw [List.mem_reverse, List.mem_ofFn] at hw
      obtain ⟨i, rfl⟩ := hw
      rw [cursorFrame_length]
      have hi := hh i.val i.isLt
      omega)
  simpa only [List.length_reverse, List.length_ofFn, Nat.mul_comm] using hb

/-- Both persistent frame banks together use polynomially many actual bits,
including framing delimiters for empty heads. -/
theorem retainedFrames_length_le (depth levels hmax : ℕ)
    (ancestors : Prefix (Representatives key) depth) (hd : depth ≤ levels)
    (hh : ∀ d < depth, h d ≤ hmax) :
    (representativeFrames h key depth ancestors).length +
      (cursorFrames h key depth ancestors).length ≤ 6 * levels * (hmax + 1) := by
  have hr := representativeFrames_length_le h key depth hmax ancestors hh
  have hc := cursorFrames_length_le h key depth hmax ancestors hh
  have hm := Nat.mul_le_mul_right (6 * (hmax + 1)) hd
  nlinarith

end Frames

section KeyEncoding

/-- The byte-key rescan's actual fresh bit is exactly the first-occurrence
predicate of the stable mathematical full signature. -/
theorem actual_fresh_iff_model {n : ℕ} {A B : Type*} [DecidableEq A]
    (actual : ℕ → A) (model : Fin n → B)
    (hkernel : ∀ i j : Fin n, actual i = actual j ↔ model i = model j)
    (candidate : Fin n) :
    (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true ↔
      ∀ j, j < candidate → model j ≠ model candidate := by
  have hb : (!(AttainedSignatures.duplicateScan actual candidate candidate)) = true ↔
      AttainedSignatures.duplicateScan actual candidate candidate = false := by
    cases AttainedSignatures.duplicateScan actual candidate candidate <;> decide
  rw [hb, AttainedSignatures.rescan_emits_iff]
  constructor
  · intro hf j hj he
    exact hf j hj ((hkernel j candidate).mpr he)
  · intro hf j hj he
    exact hf j hj ((hkernel j candidate).mp he)

end KeyEncoding

section NativeFrames

open ExecCNFTupleEnumeration SignatureTupleProgram StructuredCalls

private theorem record_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

private theorem save_outside (a : StructuredProgram.State 40 896) (i : Fin 896)
    (hf : i ≠ tupleStacks 0) (hc : i ≠ tupleStacks 2) (hr : i ≠ tupleStacks 7) :
    (saveCursorState a).stacks i = a.stacks i := by
  unfold saveCursorState
  rw [pushWordState_outside _ _ _ _ _ hr hf, pushWordState_outside _ _ _ _ _ hc hf]

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

/-- The actual record-then-save commands install precisely the dependent
child prefix in both persistent banks and empty their consumed words. -/
theorem retainFrames_state (depth : ℕ) (ancestors : Prefix (Representatives key) depth)
    (rep : Representatives key depth) (a : StructuredProgram.State 40 896)
    (hf : a.stacks (tupleStacks 0) = cursorFrames h key depth ancestors)
    (hr : a.stacks (tupleStacks 1) = representativeFrames h key depth ancestors)
    (hc : a.stacks (tupleStacks 2) = fixedBits (h depth) rep.val.val)
    (hn : a.stacks (tupleStacks 7) = fixedBits (h depth + 1) (2 ^ h depth - rep.val.val))
    (hp : a.stacks (tupleStacks 4) = []) :
    let b := saveCursorState (recordRepresentativeState a)
    b.stacks (tupleStacks 0) = cursorFrames h key (depth + 1) (Fin.snoc ancestors rep) ∧
    b.stacks (tupleStacks 1) = representativeFrames h key (depth + 1) (Fin.snoc ancestors rep) ∧
    b.stacks (tupleStacks 2) = [] ∧ b.stacks (tupleStacks 7) = [] ∧
    b.stacks (tupleStacks 4) = [] := by
  dsimp only
  have hs := saveCursorState_words (recordRepresentativeState a)
  have hrec := recordRepresentativeState_words a hp
  refine ⟨?_, ?_, hs.1, hs.2.1, ?_⟩
  · rw [hs.2.2, hrec.2.1, record_outside a (tupleStacks 7) (by decide) (by decide),
      record_outside a (tupleStacks 0) (by decide) (by decide), hc, hn, hf,
      cursorFrames_snoc, cursorFrame]
  · rw [save_outside _ (tupleStacks 1) (by decide) (by decide) (by decide),
      hrec.1, hc, hr, representativeFrames_snoc]
  · rw [save_outside _ (tupleStacks 4) (by decide) (by decide) (by decide), hrec.2.2]

end NativeFrames

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleTraversal
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleNative
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Concrete adapters for the attained-signature tuple controller

The cursor primitives are fixed in `SignatureTupleProgram`. This module
installs the actual head loader and predecessor predicate on the shared leaf
ABI, and relates their physical state to the attained-prefix traversal.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative

open BitProgram StructuredCalls SignatureTupleProgram

theorem initializeFreshState_word (a : State 40 896) :
    (initializeFreshState a).stacks (rescanStacks 22) = [false] := by
  simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, clearState]

theorem rescan_embed_controller (frame : State 40 896) (callee : State 16 24)
    (j : Fin 40) (hj : 16 ≤ j.val) :
    (embedState rescanRegisters rescanStacks frame callee).regs j = frame.regs j := by
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  dsimp [rescanRegisters] at hv
  omega

theorem candidateOutput_flag (frame : State 40 896) (regs : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val) :
    (candidateOutput frame regs W rows h candidate).regs j = frame.regs j :=
  rescan_embed_controller _ _ j hj

theorem testAvailableState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (testAvailableState a).stacks = a.stacks :=
  CounterForPrograms.testResult_stacks remainingPorts a hs

theorem initializeFreshState_controller (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) :
    (initializeFreshState a).regs j = a.regs j := by
  simp only [initializeFreshState, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    execInstr, Function.update_of_ne h0]
  exact StackRoutines.readRegs_frame a.regs 0 1 j none h0 h1

/-- Exhaustion never runs the candidate scanner. In particular the binary
fuel word can be zero even when it retains leading zero cells. -/
theorem probe_exhausted_eval (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = [])
    (hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true) :
    Eval (probeWith candidateCall) (8 * (a.stacks remainingPorts.counter).length + 9)
      a (testAvailableState a) := by
  have hf : (testAvailableState a).regs controllerPorts.available = false := by
    rw [testAvailableState_flag, hzero]
    rfl
  have he : Eval (probeWith candidateCall)
      (8 * (a.stacks remainingPorts.counter).length + 8 + (0 + 1))
      a (testAvailableState a) :=
    (testAvailable_eval a hs).seq (Eval.ite_false hf (Eval.base (.skip _)))
  simpa only [probeWith, Nat.add_assoc] using he

theorem initializeFreshState_stacks (a : State 40 896) :
    (initializeFreshState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  funext i
  by_cases hi : i = rescanStacks 22
  · subst i
    rw [Function.update_self, initializeFreshState_word]
  · simp [initializeFreshState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, clearState]

theorem probePreState_stacks (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePreState a).stacks = Function.update a.stacks (rescanStacks 22) [false] := by
  rw [probePreState, initializeFreshState_stacks, testAvailableState_stacks a hs]

/-- Preparing a candidate changes only the latch word. The whole fixed local
input projection is then the one used in the proved native rescan theorem. -/
theorem CandidateReady.probe_projection {a : State 40 896} {W : List Bool}
    {rows : List (List (List Bool))} {h : ℕ} {candidate : Fin (2 ^ h)}
    (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    projectState rescanRegisters rescanStacks (probePreState a) =
      AttainedSignatureProgram.Rescan.workState
        ((probePreState a).regs ∘ rescanRegisters) W rows
        (ExecCNFTupleEnumeration.fixedBits h candidate) []
        (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] [] := by
  apply congrArg (StructuredProgram.State.mk _)
  funext i
  change (probePreState a).stacks (rescanStacks i) = _
  rw [probePreState_stacks a hs]
  have hf (j : Fin 24) (hj : j ≠ 22) : rescanStacks j ≠ rescanStacks 22 :=
    fun he => hj (rescanStacks.injective he)
  by_cases h22 : i = 22
  · subst i
    rw [Function.update_self]
    rfl
  rw [Function.update_of_ne (hf i h22)]
  by_cases h0 : i = 0
  · subst i; exact ready.offset
  by_cases h15 : i = 15
  · subst i; exact ready.matrix
  by_cases h16 : i = 16
  · subst i; exact ready.current
  by_cases h17 : i = 17
  · subst i; exact ready.saved
  by_cases h18 : i = 18
  · subst i; exact ready.predecessor
  rw [ready.scratch i h0 h15 h16 h17 h18 h22]
  fin_cases i <;> simp_all

theorem CursorWords.remaining_value {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.value (a.stacks remainingPorts.counter) = 2 ^ h - c := by
  rw [hw.remaining]
  apply ExecCNFTupleEnumeration.fixedBits_value
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  rw [pow_succ]
  omega

theorem CursorWords.available {a : State 40 896} {h c : ℕ}
    (hw : CursorWords a h c) :
    CounterPrograms.isZero (a.stacks remainingPorts.counter) = decide (c = 2 ^ h) := by
  have hv := hw.remaining_value
  have hr := hw.range
  by_cases he : c = 2 ^ h
  · simp only [he, decide_true]
    apply (CounterPrograms.isZero_eq_true_iff _).mpr
    rw [hv, he, Nat.sub_self]
  · simp only [he, decide_false]
    apply (CounterPrograms.isZero_eq_false_iff _).mpr
    omega


section CursorStorage

open SignatureTupleDFS SignatureTupleTraversal

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem AncestorStorage.frame_bound {levels base depth : ℕ}
    {ancestors : Prefix (Representatives key) depth} {a : State 40 896}
    (ha : AncestorStorage h key levels base depth ancestors a) (hmax : ℕ)
    (hh : ∀ d < levels, h d ≤ hmax) :
    (a.stacks (tupleStacks 0)).length + (a.stacks (tupleStacks 1)).length ≤
      6 * levels * (hmax + 1) := by
  rw [ha.cursors, ha.representatives, Nat.add_comm]
  exact retainedFrames_length_le h key depth levels hmax ancestors ha.depth_le
    (fun d hd => hh d (hd.trans_le ha.depth_le))


end CursorStorage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureRescanBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Physical effects of one full-signature probe

The input readiness facts describe actual words. The native predicate itself
supplies the run; its returned freshness is the first-occurrence predicate for
the complete integer signature.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open AttainedSignatureProgram.Rescan

theorem probe_stacks (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) :
    (probePostState a out W rows h candidate).stacks =
      Function.update (Function.update a.stacks (rescanStacks 17)
        (naturalKey W rows h candidate)) (rescanStacks 22)
        [!(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)] := by
  classical
  let pre := probePreState a
  let initial := workState (pre.regs ∘ rescanRegisters) W rows
    (ExecCNFTupleEnumeration.fixedBits h candidate) []
    (ExecCNFTupleEnumeration.fixedBits h 0) [] false [] []
  let key := naturalKey W rows h candidate
  let fresh := !(AttainedSignatures.duplicateScan (naturalKey W rows h) candidate candidate)
  have hz : ExecCNFTupleEnumeration.fixedBits h 0 = List.replicate h false :=
    ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
      (by simp [ExecCNFTupleEnumeration.fixedBits_value h 0 (Nat.pow_pos (by decide))])
  have hlocal : (workState out W rows (ExecCNFTupleEnumeration.fixedBits h candidate)
      key (List.replicate h false) [] fresh [] []).stacks =
      Function.update (Function.update initial.stacks 17 key) 22 [fresh] := by
    dsimp [initial]
    rw [hz]
    funext i
    fin_cases i <;> simp [workState]
  have hemb : Function.extend rescanStacks initial.stacks pre.stacks = pre.stacks := by
    change (embedState rescanRegisters rescanStacks pre initial).stacks = pre.stacks
    have hi : projectState rescanRegisters rescanStacks pre = initial := ready.probe_projection hs
    rw [← hi, embedState_project _ _ _ rescanRegisters.injective rescanStacks.injective]
  change Function.extend rescanStacks _ pre.stacks = _
  rw [hlocal, ProgramLinking.extend_update rescanStacks.injective,
    ProgramLinking.extend_update rescanStacks.injective, hemb]
  change Function.update (Function.update (probePreState a).stacks (rescanStacks 17) key)
    (rescanStacks 22) [fresh] = _
  rw [probePreState_stacks a hs]
  funext j
  by_cases h17 : j = rescanStacks 17
  · subst j
    simp only [Function.update_self, Function.update_of_ne
      (by decide : rescanStacks 17 ≠ rescanStacks 22)]
    rfl
  · by_cases h22 : j = rescanStacks 22
    · subst j; simp only [Function.update_self]; rfl
    · simp only [Function.update_of_ne h17, Function.update_of_ne h22]

theorem probe_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) (j : Fin 896)
    (hk : j ≠ rescanStacks 17) (hf : j ≠ rescanStacks 22) :
    (probePostState a out W rows h candidate).stacks j = a.stacks j := by
  rw [probe_stacks a out W rows h candidate ready hs]
  rw [Function.update_of_ne hf, Function.update_of_ne hk]

theorem probe_preserves_cursor (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (cursor : CursorWords a h candidate) :
    CursorWords (probePostState a out W rows h candidate) h candidate := by
  have hc := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    candidatePorts.counter (by decide) (by decide)
  have hr := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    remainingPorts.counter (by decide) (by decide)
  have hcs := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    candidatePorts.scratch (by decide) (by decide)
  have hrs := probe_stack_frame a out W rows h candidate ready cursor.decrementScratch
    remainingPorts.scratch (by decide) (by decide)
  exact ⟨cursor.range, hc ▸ cursor.value, hc ▸ cursor.width,
    fun hi => hc.trans (cursor.exact hi), hr.trans cursor.remaining,
    hcs.trans cursor.incrementScratch, hrs.trans cursor.decrementScratch⟩

theorem test_available_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (ha : j ≠ controllerPorts.available) :
    (testAvailableState a).regs j = a.regs j := by
  have h2 : j ≠ remainingPorts.register 2 := by
    intro he
    have hv := congrArg Fin.val he
    change j.val = 2 at hv
    omega
  simp only [testAvailableState, CounterForPrograms.testResult,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne ha, Function.update_of_ne h2]
  apply embedState_register_frame
  rintro ⟨i, hi⟩
  have hv := congrArg Fin.val hi
  have hil := i.isLt
  change i.val = j.val at hv
  omega

theorem probe_register_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (j : Fin 40) (hj : 16 ≤ j.val)
    (ha : j ≠ controllerPorts.available) (hf : j ≠ controllerPorts.fresh) :
    (probePostState a out W rows h candidate).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro he; subst j; norm_num at hj
  change readRegs (candidateOutput (probePreState a) out W rows h candidate).regs
    controllerPorts.fresh 0 _ j = _
  rw [StackRoutines.readRegs_frame _ _ _ _ _ hf h0,
    candidateOutput_flag _ _ _ _ _ _ _ hj]
  rw [probePreState, initializeFreshState_controller _ _ h0 h1]
  exact test_available_register_frame a j (by omega) ha

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureRescanBridge
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRefinement
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual state refinements for the fixed attained-signature controller.
Each lemma follows concrete commands already installed in the native ABI. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative
open SignatureTupleDFS SignatureTupleTraversal

theorem recordRepresentative_outside (a : State 40 896) (i : Fin 896)
    (hr : i ≠ tupleStacks 1) (hp : i ≠ tupleStacks 4) :
    (recordRepresentativeState a).stacks i = a.stacks i := by
  unfold recordRepresentativeState
  rw [pushWordState_outside _ _ _ _ _ hp hr]
  simp [copyState, StackRoutines.copyStacks, hp]

theorem retainedState_outside (a : State 40 896) (i : Fin 896)
    (h0 : i ≠ tupleStacks 0) (h1 : i ≠ tupleStacks 1)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (retainedState a).stacks i = a.stacks i := by
  unfold retainedState saveCursorState
  rw [pushWordState_outside _ _ _ _ _ h7 h0,
    pushWordState_outside _ _ _ _ _ h2 h0, recordRepresentative_outside a i h1 h4]

theorem retainedState_register (a : State 40 896) (j : Fin 40)
    (h0 : j ≠ 0) (h1 : j ≠ 1) : (retainedState a).regs j = a.regs j := by
  unfold retainedState saveCursorState recordRepresentativeState
  rw [pushWordState_register_frame _ _ _ _ j h0 h1,
    pushWordState_register_frame _ _ _ _ j h0 h1,
    pushWordState_register_frame _ _ _ _ j h0 h1]
  exact StackRoutines.readRegs_frame a.regs 0 1 j none h0 h1

theorem descendLevelState_outside (a : State 40 896) (i : Fin 896)
    (h6 : i ≠ tupleStacks 6) (h9 : i ≠ tupleStacks 9) :
    (descendLevelState a).stacks i = a.stacks i := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, h6, h9]

theorem descendLevelState_active (a : State 40 896) :
    (descendLevelState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  simp [descendLevelState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr, readRegs,
    controllerPorts]

theorem descendClearState_cleared (a : State 40 896) :
    ∀ i ∈ currentHeadPorts, (descendClearState a).stacks i = [] := by
  intro i hi
  rw [descendClearState, clearWordsState_stacks, ite_eq_left hi]

theorem descendClearState_stack (a : State 40 896) (i : Fin 896)
    (hi : i ∉ currentHeadPorts) :
    (descendClearState a).stacks i = (descendLevelState (retainedState a)).stacks i := by
  rw [descendClearState, clearWordsState_stacks, ite_eq_right hi]

theorem descendClearState_active (a : State 40 896) :
    (descendClearState a).regs controllerPorts.active = a.regs controllerPorts.active := by
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide),
    descendLevelState_active, retainedState_register _ _ (by decide) (by decide)]

theorem descendClearState_leaf (a : State 40 896) (address : ℕ)
    (hr : a.stacks (tupleStacks 6) = [true])
    (hz : a.stacks (tupleStacks 9) = List.replicate address true) :
    (descendClearState a).regs controllerPorts.leaf = true := by
  have hw := descendLevelState_words (retainedState a) 0 address
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hz)
  rw [descendClearState, clearWordsState_register_frame _ _ _ (by decide) (by decide)]
  exact hw.2.2

theorem rootAscendState_halt (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = []) :
    (rootAscendState a).regs controllerPorts.active = false := by
  rw [rootAscendState, testParentState_flag, clearWordsState_stacks]
  simp only [show tupleStacks 0 ∉ currentHeadPorts by decide, ite_false, hf, ne_eq,
    not_true_eq_false, decide_false]

/-- An exhausted root, including return from the sole empty tuple, clears
its current arrays and halts without attempting to pop a missing frame. -/
theorem rootAscend_eval (loadHead : Cmd 40 896) (a : State 40 896)
    (hf : a.stacks (tupleStacks 0) = []) :
    Eval (ascendWith loadHead) (clearWordsTime currentHeadPorts a + 2) a
      (rootAscendState a) := by
  have hbranch : Eval (.ite controllerPorts.active (resumeParentWith loadHead) (.base .skip))
      1 (rootAscendState a) (rootAscendState a) :=
    .ite_false (rootAscendState_halt a hf) (.base (.skip _))
  have he := (clearWords_eval currentHeadPorts a).seq
    ((testParent_eval (clearWordsState currentHeadPorts a)).seq hbranch)
  simpa only [ascendWith, leaveHeadCommand, rootAscendState, Nat.add_assoc] using he

theorem clearWordsTime_le_on (ports : List (Fin 896)) (a : State 40 896) (B : ℕ)
    (hb : ∀ i ∈ ports, (a.stacks i).length ≤ B) :
    clearWordsTime ports a ≤ ports.length * (2 * B + 3) := by
  induction ports generalizing a with
  | nil => simp [clearWordsTime]
  | cons src rest ih =>
    have hsrc := hb src (by simp)
    have hrest : ∀ i ∈ rest, ((clearState src a).stacks i).length ≤ B := by
      intro i hi
      by_cases he : i = src
      · subst i
        simp [clearState]
      · simpa [clearState, he] using hb i (by simp [hi])
    have htail := ih (clearState src a) hrest
    simp only [clearWordsTime, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem exhausted_root_iteration (loadHead visit : Cmd 40 896)
    (a : State 40 896) (F : ℕ)
    (hl : a.regs controllerPorts.leaf = false)
    (hf : a.stacks (tupleStacks 0) = [])
    (hs : a.stacks remainingPorts.scratch = [])
    (hz : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true)
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∃ n,
      Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a
        (rootAscendState (testAvailableState a)) ∧
      (rootAscendState (testAvailableState a)).regs controllerPorts.active = false ∧
      n + 1 ≤ 8 * (a.stacks remainingPorts.counter).length + 8 * (2 * F + 3) + 14 := by
  have hp := probe_exhausted_eval a hs hz
  have hwords := testAvailableState_stacks a hs
  have hframes : (testAvailableState a).stacks (tupleStacks 0) = [] := by rw [hwords, hf]
  have ha := rootAscend_eval loadHead (testAvailableState a) hframes
  have hav : (testAvailableState a).regs controllerPorts.available = false := by
    rw [testAvailableState_flag, hz]
    rfl
  have hc := clearWordsTime_le_on currentHeadPorts (testAvailableState a) F
    (fun i _ => by rw [hwords]; exact hframe i)
  change clearWordsTime currentHeadPorts (testAvailableState a) ≤ 8 * (2 * F + 3) at hc
  refine ⟨_, .exhausted hl hp hav ha, rootAscendState_halt _ hframes, ?_⟩
  omega


/-- The presence test does not change any stack, and cleanup leaves both
persistent prefix banks intact. -/
theorem checkedReturnState_stack (a : State 40 896) (i : Fin 896) :
    (rootAscendState a).stacks i = if i ∈ currentHeadPorts then [] else a.stacks i :=
  clearWordsState_stacks currentHeadPorts a i


/-- Current-head cleanup does not erase the newly attained child prefix or
its unary depth/address words. This also covers internal children. -/
theorem descend_ancestor_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896) (hd : depth < levels)
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4) = []) :
    AncestorStorage h key levels base (depth + 1) (Fin.snoc ancestors rep) (descendClearState a) := by
  have hf := retainFrames_state h key depth ancestors rep a
    ha.cursors ha.representatives (hw.exact rep.val.isLt) hw.remaining hp
  have heq : levels - depth = levels - (depth + 1) + 1 := by omega
  have hr : (retainedState a).stacks (tupleStacks 6) =
      List.replicate (levels - (depth + 1) + 1) true := by
    rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      ha.heads, heq]
  have hz : (retainedState a).stacks (tupleStacks 9) = List.replicate (base + depth) true := by
    rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha.address
  have hl := descendLevelState_words (retainedState a) (levels - (depth + 1)) (base + depth) hr hz
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [descendClearState_stack _ _ (by decide), hl.1]
  · rw [descendClearState_stack _ _ (by decide), hl.2.1]
    simp [Nat.add_assoc]
  · rw [descendClearState_active]
    exact ha.active

section LeafStorage

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem descend_leaf_storage (depth base : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896)
    (ha : AncestorStorage h key (depth + 1) base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val)
    (hp : a.stacks (tupleStacks 4) = []) :
    LeafStorage h key (depth + 1) base (Fin.snoc ancestors rep) (descendClearState a) := by
  have hf := retainFrames_state h key depth ancestors rep a
    ha.cursors ha.representatives (hw.exact rep.val.isLt) hw.remaining hp
  have hr : a.stacks (tupleStacks 6) = [true] := by simpa using ha.heads
  have hl := descendLevelState_words (retainedState a) 0 (base + depth)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr)
    (by rw [retainedState_outside _ _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact ha.address)
  refine ⟨⟨le_rfl, ?_, ?_, ?_, ?_, ?_⟩, descendClearState_leaf a (base + depth) hr ha.address,
    descendClearState_cleared a⟩
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.1
  · rw [descendClearState_stack _ _ (by decide), descendLevelState_outside _ _ (by decide) (by decide)]
    exact hf.2.1
  · rw [descendClearState_stack _ _ (by decide), hl.1]
    simp
  · rw [descendClearState_stack _ _ (by decide), hl.2.1]
    simp [Nat.add_assoc]
  · rw [descendClearState_active]
    exact ha.active

end LeafStorage

theorem descendClearState_outside_tuple (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) : (descendClearState a).stacks i = a.stacks i := by
  have hc : i ∉ currentHeadPorts := by
    simp only [currentHeadPorts, List.mem_cons, List.mem_nil_iff, or_false, not_or]
    exact ⟨hi 2, hi 3, hi 4, hi 5, hi 7, hi 8, hi 10, hi 11⟩
  rw [descendClearState_stack a i hc, descendLevelState_outside _ _ (hi 6) (hi 9),
    retainedState_outside _ _ (hi 0) (hi 1) (hi 2) (hi 4) (hi 7)]

theorem exhausted_root_run_space (loadHead visit : Cmd 40 896)
    (a : State 40 896) (F : ℕ) (hleaf : a.regs controllerPorts.leaf = false)
    (hframes : a.stacks (tupleStacks 0) = [])
    (hs : a.stacks remainingPorts.scratch = [])
    (hz : CounterPrograms.isZero (a.stacks remainingPorts.counter) = true)
    (hframe : ∀ i, (a.stacks i).length ≤ F) :
    ∃ n,
      Eval (body controllerPorts (assembleRoutines loadHead candidateCall visit)) n a
        (rootAscendState (testAvailableState a)) ∧
      (rootAscendState (testAvailableState a)).regs controllerPorts.active = false ∧
      (∀ i, ((rootAscendState (testAvailableState a)).stacks i).length ≤ F) ∧
      (∀ prefixSteps intermediate, prefixSteps ≤ n + 1 →
        Trace (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
          prefixSteps (a.withPC (some (compiled
            (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤ 2000 * (F + 1)) ∧
      n + 1 ≤ 24 * F + 38 := by
  obtain ⟨n, hi, hhalt, htime⟩ := exhausted_root_iteration loadHead visit a F hleaf hframes hs hz hframe
  have htime' : n + 1 ≤ 24 * F + 38 := by
    have hf := hframe remainingPorts.counter
    omega
  refine ⟨n, hi.eval, hhalt, ?_, ?_, htime'⟩
  · intro i
    rw [checkedReturnState_stack, testAvailableState_stacks a hs]
    split_ifs
    · simp
    · exact hframe i
  · have hb := StructuredSpace.local_stack_bound
      (compiled (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0)
      (a := a.withPC (some (compiled
        (body controllerPorts (assembleRoutines loadHead candidateCall visit)) 0 0).entry))
      (steps := 24 * F + 38) (StreamResources.dataBits_le_mul _ hframe)
    intro p q hp hq i
    exact (hb p q (by omega) hq i).trans (by omega)

theorem fresh_descent_stack_frame (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2 ^ h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch = []) (i : Fin 896)
    (hi : ∀ j : Fin 12, i ≠ tupleStacks j) (hf : i ≠ rescanStacks 22) :
    (descendClearState (probePostState a out W rows h candidate)).stacks i = a.stacks i := by
  rw [descendClearState_outside_tuple _ i hi]
  exact SignatureRescanBridge.probe_stack_frame a out W rows h candidate ready hs i (hi 3) hf

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleBranchSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix composition for the actual exhausted and leaf branches of the
attained-signature controller. The component executions are the installed
probe, visitor and ascent commands, and every caller stack is covered. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace

open BitProgram StructuredCalls SignatureTupleProgram SignatureTupleNative

/-- Inverting the installed body preserves its actual measured execution;
it does not choose a second run or replace the visitor. -/
theorem iteration_of_eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (he : Eval (body p q) n a b) :
    Iteration p q n a b := by
  cases he with
  | ite_true hl hleaf =>
    cases hleaf with
    | seq hv ha => exact .leaf hl hv ha
  | ite_false hl hscan =>
    cases hscan with
    | seq hp havailable =>
      cases havailable with
      | ite_false ha hasc =>
        simpa only [Nat.add_assoc] using Iteration.exhausted hl hp ha hasc
      | ite_true ha hfresh =>
        cases hfresh with
        | ite_true hf hd =>
          simpa only [Nat.add_assoc] using Iteration.fresh hl hp ha hf hd
        | ite_false hf hn =>
          simpa only [Nat.add_assoc] using Iteration.duplicate hl hp ha hf hn

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleBranchSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete head reloads for the attained-signature DFS.  The matrix comes
from the fixed native integer-entry machine, and each reload restores one
fixed retained-word bound before the next candidate scan. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage


/-- All raw incidence rows are present in the scanner, with polynomial
coefficient word lengths. No coordinate grid is materialized. -/
theorem shifted_rows_bounds (s : Native.Inputs) (z L : ℕ) (W : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (hW : W.length≤L)
    (hr : LayoutMatrixProgram.MatrixRel s.relation s.columnLength s.D
      (selectedHeads s.n s.rows s.low z) raw)
    (hy : List.Forall₂ (List.Forall₂ (BucketProgram.shiftedWord W)) raw shifted) :
    shifted.length=s.D ∧
      (∀ row∈shifted, row.length=(selectedHeads s.n s.rows s.low z).length) ∧
      ∀ row∈shifted, ∀ x∈row, x.length≤3*(s.columnLength+L)+1 := by
  obtain ⟨c,hc,hentry⟩ := SignatureHeadLoader.shiftedMatrix_typed W s.relation
    s.columnLength s.D (selectedHeads s.n s.rows s.low z) raw shifted hr hy
  subst shifted
  refine ⟨by simp, ?_, ?_⟩
  · intro row hrow
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    simp
  · intro row hrow x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hrow
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    obtain ⟨pair,_,hpair,hshift⟩ := hentry j i
    have hlength := hshift.2
    unfold LayoutMatrixProgram.pairLength at hpair
    omega

section Storage
open SignatureTupleDFS SignatureTupleTraversal


/-- Internal descent retains only attained frames and the unary depth. Its
boundary bound depends on depth and word lengths, never on visited nodes. -/
theorem descend_endpoint_bound (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth hmax F : ℕ)
    (ancestors : Prefix (Representatives key) depth) (rep : Representatives key depth)
    (a : State 40 896) (hd : depth<levels)
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) rep.val.val) (hp : a.stacks (tupleStacks 4)=[])
    (hh : ∀ d<levels, h d≤hmax)
    (hcap : 6*levels*(hmax+1)+(base+levels)≤F)
    (hframe : ∀ i, (a.stacks i).length≤F) :
    ∀ i, ((descendClearState a).stacks i).length≤F := by
  have hb := descend_ancestor_storage h key levels base depth ancestors rep a hd ha hw hp
  have hf := hb.frame_bound h key hmax hh
  have hcleared := descendClearState_cleared a
  intro i
  by_cases hi : ∃ j : Fin 12, i=tupleStacks j
  · obtain ⟨j,rfl⟩ := hi
    fin_cases j
    · change ((descendClearState a).stacks (tupleStacks 0)).length≤F
      omega
    · change ((descendClearState a).stacks (tupleStacks 1)).length≤F
      omega
    · change ((descendClearState a).stacks (tupleStacks 2)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 3)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 4)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 5)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 6)).length≤F
      rw [hb.heads, List.length_replicate]
      omega
    · change ((descendClearState a).stacks (tupleStacks 7)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 8)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 9)).length≤F
      rw [hb.address, List.length_replicate]
      omega
    · change ((descendClearState a).stacks (tupleStacks 10)).length≤F
      rw [hcleared _ (by decide)]; simp
    · change ((descendClearState a).stacks (tupleStacks 11)).length≤F
      rw [hcleared _ (by decide)]; simp
  · rw [descendClearState_outside_tuple a i (fun j hj => hi ⟨j,hj⟩)]
    exact hframe i


private theorem low_outside_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  have := i.isLt
  omega

private theorem master_not_latch (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i≠rescanStacks 22 := by
  intro he
  have hv := congrArg Fin.val he
  have heq : i=(362 : Fin 768) := Fin.ext hv
  subst i
  exact (by decide : (362 : Fin 768)∉SignatureHeadLoader.masters) hi

/-- The actual probe and attained descent preserve every loader source word
and native cache; only bounded cursor frames and the scanner latch change. -/
theorem fresh_descent_masters (a : State 40 896) (out : Fin 16 → Bool)
    (W : List Bool) (rows : List (List (List Bool))) (h : ℕ)
    (candidate : Fin (2^h)) (ready : CandidateReady a W rows h candidate)
    (hs : a.stacks remainingPorts.scratch=[])
    (base : Data) (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (descendClearState (probePostState a out W rows h candidate))) := by
  constructor
  intro i hi
  exact (fresh_descent_stack_frame a out W rows h candidate ready hs
    (SignatureHeadLoader.lowStacks i) (low_outside_tuple i) (master_not_latch i hi)).trans
    (hm.stored i hi)


/-- Root exhaustion preserves the last root address, so the next pair can
initialize_ its traversal from low649 again. -/
theorem exhausted_root_address649 (a : State 40 896)
    (hs : a.stacks remainingPorts.scratch=[]) :
    (rootAscendState (testAvailableState a)).stacks 649=a.stacks 649 := by
  rw [checkedReturnState_stack,ite_eq_right (by decide),testAvailableState_stacks a hs]

end Storage

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Shared actual produced input data for the tuple controller and visitor.
The record contains source words, native readiness and paid cache semantics;
it contains no evaluator, resource contract, or successful execution premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

namespace ProducedSource

theorem headSize_le (s : ProducedSource) (depth : ℕ) : s.headSize depth ≤ s.input.n :=
  Bounds.selectedHeads_length ..

end ProducedSource


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

theorem PersistentPort.not_fresh {i : Fin 896} (h : PersistentPort i) : i≠rescanStacks 22 := by
  intro he
  have hp := h.outsideWork
  have hv := congrArg Fin.val he
  change i.val=362 at hv
  rcases hp with hp|hp <;> omega

theorem PersistentPort.not_current {i : Fin 896} (h : PersistentPort i) : i∉currentHeadPorts := by
  simp only [currentHeadPorts,List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨h.tuple 2,h.tuple 3,h.tuple 4,h.tuple 5,h.tuple 7,h.tuple 8,h.tuple 10,h.tuple 11⟩

private theorem low_not_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  omega

private theorem probe_ancestors (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth) (candidate : Fin (2^h depth))
    (a : State 40 896) (out : Fin 16 → Bool) (W : List Bool)
    (rows : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth ancestors a)
    (hw : CursorWords a (h depth) candidate.val)
    (ready : CandidateReady a W rows (h depth) candidate) :
    AncestorStorage h key levels base depth ancestors
      (probePostState a out W rows (h depth) candidate) := by
  have frame (i : Fin 896) (hk : i≠rescanStacks 17) (hl : i≠rescanStacks 22) :=
    SignatureRescanBridge.probe_stack_frame a out W rows (h depth) candidate ready
      hw.decrementScratch i hk hl
  refine ⟨ha.depth_le,?_,?_,?_,?_,?_⟩
  · exact (frame _ (by decide) (by decide)).trans ha.cursors
  · exact (frame _ (by decide) (by decide)).trans ha.representatives
  · exact (frame _ (by decide) (by decide)).trans ha.heads
  · exact (frame _ (by decide) (by decide)).trans ha.address
  · exact (SignatureRescanBridge.probe_register_frame a out W rows (h depth) candidate
      controllerPorts.active (by decide) (by decide) (by decide)).trans ha.active

theorem final_descend_cursor (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (rep : Representatives key depth.val)
    (a : State 40 896) (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hw : CursorWords a (h depth.val) rep.val.val) (hp : a.stacks (tupleStacks 4)=[])
    (hlast : depth.val+1=levels) :
    CursorStorage h key levels base
      (enter key levels (depth.val+1) depth.isLt (Fin.snoc ancestors rep)) (descendClearState a) := by
  cases levels with
  | zero => exact Fin.elim0 depth
  | succ m =>
    have he : depth=Fin.last m := Fin.ext (by simpa only [Fin.val_last] using Nat.add_right_cancel hlast)
    subst depth
    simpa only [Fin.val_last,enter_leaf] using
      (CursorStorage.leaf (descend_leaf_storage h key m base ancestors rep a ha hw hp))


/-- The last attained head reaches the actual cleaned tuple visitor state.
There is one such state per attained full tuple, including empty head words. -/
theorem fresh_final_step (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (visit : Cmd 40 896) (depth : Fin s.input.r)
    (ancestors : Prefix (Representatives s.key) depth.val)
    (rep : Representatives s.key depth.val) (a : State 40 896)
    (ha : ScanBoundary s F depth ancestors rep.val.val a) (hlast : depth.val+1=s.input.r) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      Boundary s F (enter s.key s.input.r (depth.val+1) depth.isLt (Fin.snoc ancestors rep)) b ∧
      n+1 ≤ (rep.val.val+1)*eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  obtain ⟨raw,shifted,hr,hy,hready⟩ := ha.matrix.data
  have ready := hready rep.val.isLt
  let C := 3*(s.input.columnLength+s.bound)+1
  have hshape := shifted_rows_bounds s.input (s.base+depth.val) s.bound
    (s.source.stacks 141) raw shifted (s.bounded 141) hr hy
  have hbud := scanner_caps_polynomial s.input s.source s.bound (s.base+depth.val)
    s.ready s.bounded (s.source.stacks 141) (s.bounded 141) raw shifted hr hy
  have hactual := (actual_fresh_iff_model _ _ (scan_kernel s depth.val raw shifted hr hy) rep.val).mpr
    rep.property
  have hheads : a.stacks (tupleStacks 6)=[true] := by
    rw [ha.heads]
    have he : s.input.r-depth.val=1 := by omega
    rw [he]
    rfl
  obtain ⟨n,out,he,hprefix,ht⟩ := fresh_leaf_run_space loadHead visit a (s.source.stacks 141)
    shifted (s.headSize depth.val) C F (s.base+depth.val) rep.val ready ha.toCursorWords
    hshape.2.1 hshape.2.2 ha.leaf hactual ha.payload hheads ha.address ha.bound cap.positive
    ((Nat.add_le_add_right (s.headSize_le depth.val) 1).trans cap.cursor)
    (hbud.2.2.trans cap.scanner) (hbud.2.1.trans cap.scanner)
  let b := probePostState a out (s.source.stacks 141) shifted (s.headSize depth.val) rep.val
  have hb := probe_endpoint_bound a out (s.source.stacks 141) shifted (s.headSize depth.val)
    C F rep.val ready ha.decrementScratch hshape.2.1 hshape.2.2 ha.bound cap.positive
    (hbud.2.2.trans cap.scanner)
  have hcursor := SignatureRescanBridge.probe_preserves_cursor a out (s.source.stacks 141)
    shifted (s.headSize depth.val) rep.val ready ha.toCursorWords
  have hanc := probe_ancestors s.headSize s.key s.input.r s.base depth.val ancestors rep.val
    a out (s.source.stacks 141) shifted ha.toAncestorStorage ha.toCursorWords ready
  have hp : b.stacks (tupleStacks 4)=[] :=
    (SignatureRescanBridge.probe_stack_frame a out (s.source.stacks 141) shifted
      (s.headSize depth.val) rep.val ready ha.decrementScratch _ (by decide) (by decide)).trans ha.payload
  have hstorage := final_descend_cursor s.headSize s.key s.input.r s.base depth ancestors rep b
    hanc hcursor hp hlast
  have hend := descend_endpoint_bound s.headSize s.key s.input.r s.base depth.val s.input.n F
    ancestors rep b depth.isLt hanc hcursor hp (fun d _ => s.headSize_le d) (by have := cap.frames; omega) hb
  have hmasters := fresh_descent_masters a out (s.source.stacks 141) shifted (s.headSize depth.val)
    rep.val ready ha.decrementScratch s.masters ha.masters
  have hnext : Boundary s F
      (enter s.key s.input.r (depth.val+1) depth.isLt (Fin.snoc ancestors rep)) (descendClearState b) := by
    rw [enter,dite_eq_left hlast] at hstorage ⊢
    cases hstorage with
    | leaf hl =>
      apply Boundary.leaf
      refine ⟨hl,hend,hmasters,?_⟩
      intro hz
      have hp := depth.isLt
      omega
  refine ⟨n,descendClearState b,SignatureTupleBranchSpace.iteration_of_eval he,hnext,?_,?_,?_⟩
  · apply ht.trans
    apply Nat.mul_le_mul_left
    have hp : AttainedSignatureProgram.Rescan.polynomialBudget (s.source.stacks 141)
        shifted (s.headSize depth.val) C ≤ scannerEnvelope s.bound := hbud.1
    unfold eventPolynomial
    omega
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by unfold prefixEnvelope; omega)

  · intro i hi
    exact fresh_descent_stack_frame a out (s.source.stacks 141) shifted (s.headSize depth.val)
      rep.val ready ha.decrementScratch i hi.tuple hi.not_fresh

private theorem low_not_current (i : Fin 768) : SignatureHeadLoader.lowStacks i∉currentHeadPorts := by
  simp only [currentHeadPorts,List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨low_not_tuple i 2,low_not_tuple i 3,low_not_tuple i 4,low_not_tuple i 5,
    low_not_tuple i 7,low_not_tuple i 8,low_not_tuple i 10,low_not_tuple i 11⟩

/-- Exhausting the root returns low649 unchanged, so another finite-
difference pair starts at the same node base. -/
theorem exhausted_root_step (s : ProducedSource) (F : ℕ) (visit : Cmd 40 896)
    (depth : Fin s.input.r) (ancestors : Prefix (Representatives s.key) depth.val)
    (a : State 40 896) (ha : ScanBoundary s F depth ancestors (2^s.headSize depth.val) a)
    (hd : depth.val=0) :
    ∃ n b, Iteration controllerPorts (assembleRoutines loadHead candidateCall visit) n a b ∧
      HaltBoundary s F b ∧ n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts
        (assembleRoutines loadHead candidateCall visit)) 0 0) p
        (a.withPC (some (compiled (body controllerPorts
          (assembleRoutines loadHead candidateCall visit)) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧ ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hframes : a.stacks (tupleStacks 0)=[] := by
    rw [ha.cursors]
    simp only [cursorFrames,hd,List.ofFn_zero,List.reverse_nil,List.flatten_nil]
  have hzero : CounterPrograms.isZero (a.stacks remainingPorts.counter)=true := by
    rw [ha.toCursorWords.available]
    simp
  obtain ⟨n,he,halt,hbound,hprefix,ht⟩ := exhausted_root_run_space loadHead visit a F
    ha.leaf hframes ha.decrementScratch hzero ha.bound
  have hb : HaltBoundary s F (rootAscendState (testAvailableState a)) := by
    refine ⟨halt,hbound,?_,?_⟩
    · constructor
      intro i hi
      change (rootAscendState (testAvailableState a)).stacks (SignatureHeadLoader.lowStacks i)=_
      rw [checkedReturnState_stack,ite_eq_right (low_not_current i),testAvailableState_stacks a ha.decrementScratch]
      exact ha.masters.stored i hi
    · rw [exhausted_root_address649 a ha.decrementScratch,ha.address649,hd,Nat.add_zero]
  refine ⟨n,_,SignatureTupleBranchSpace.iteration_of_eval he,hb,?_,?_,?_⟩
  · unfold eventPolynomial
    omega
  · intro p q hp hq i
    exact (hprefix p q hp hq i).trans (by unfold prefixEnvelope; omega)

  · intro i hi
    rw [checkedReturnState_stack,ite_eq_right hi.not_current,testAvailableState_stacks a ha.decrementScratch]

/-- Every nonleaf semantic edge is realized by the concrete installed body.
It preserves every physical query master and the pair accumulator bytes. -/
theorem nonleaf_step (s : ProducedSource) (F leafCost : ℕ) (cap : RetainedCap s F)
    (event : Event s.key s.input.r) (before after : Cursor s.key s.input.r)
    (a : State 40 896) (step : Step s.key s.input.r event before after)
    (ha : Boundary s F before a)
    (hnoleaf : ∀ ancestors,event≠Event.leaf ancestors) :
    a.regs controllerPorts.active=true ∧ ∃ n b,
      Iteration controllerPorts routines n a b ∧ Boundary s F after b ∧
      n+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (body controllerPorts routines) 0 0) p
        (a.withPC (some (compiled (body controllerPorts routines) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  unfold routines
  cases step with
  | fresh depth ancestors rep =>
    cases ha with
    | scan hs =>
      refine ⟨hs.active,?_⟩
      by_cases hd : depth.val + 1 < s.input.r
      · obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := fresh_internal_step s F cap
          QueryVisitorProgram.visitor depth ancestors rep a hs hd
        refine ⟨n,b,he,?_,?_,hspace,hframe⟩
        · rw [enter_internal s.key s.input.r (depth.val+1) hd]
          exact Boundary.scan hb
        · simpa only [costWeight,Nat.mul_comm] using ht
      · have hd' : depth.val+1=s.input.r := by have := depth.isLt; omega
        obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := fresh_final_step s F cap
          QueryVisitorProgram.visitor depth ancestors rep a hs hd'
        exact ⟨n,b,he,hb,by simpa only [costWeight,Nat.mul_comm] using ht,hspace,hframe⟩
  | duplicate depth ancestors candidate hdup =>
    cases ha with
    | scan hs =>
      obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := duplicate_step s F cap QueryVisitorProgram.visitor
        depth ancestors candidate a hs hdup
      refine ⟨hs.active,n,b,he,Boundary.scan hb,?_,hspace,?_⟩
      · simpa only [costWeight,Nat.mul_comm] using ht
      · intro i hi
        exact hframe i (hi.tuple 2) (hi.tuple 7) hi.not_fresh
  | exhausted depth ancestors =>
    cases ha with
    | scan hs =>
      refine ⟨hs.active,?_⟩
      rcases depth with ⟨depth,hd⟩
      cases depth with
      | zero =>
        obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := exhausted_root_step s F QueryVisitorProgram.visitor
          ⟨0,hd⟩ ancestors a hs rfl
        exact ⟨n,b,he,Boundary.halt hb,ht,hspace,hframe⟩
      | succ depth =>
        obtain ⟨n,b,he,hb,ht,hspace,hframe⟩ := exhausted_successor_step s F cap
          QueryVisitorProgram.visitor ⟨depth,by omega⟩ hd ancestors a hs
        exact ⟨n,b,he,Boundary.scan hb,ht,hspace,hframe⟩
  | leaf ancestors => exact False.elim (hnoleaf ancestors rfl)

theorem queryMaster_persistent (i : Fin 896) (hi : i∈QueryTupleState.masterPorts) :
    PersistentPort i := by
  simp only [QueryTupleState.masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact ⟨by decide,by decide,by decide⟩

theorem query_frame_of_persistent (a b : State 40 896)
    (hf : ∀ i,PersistentPort i → b.stacks i=a.stacks i) :
    QueryTupleState.QueryMasterFrame a b :=
  ⟨fun i hi => hf i (queryMaster_persistent i hi)⟩

/-- Exact nonleaf preservation of the enriched arithmetic relation. The
ring/cache words, masks and851 dictionary are transported by actual frames. -/
theorem nonleaf_rel_step_oai (s : ProducedSource) (F leafCost : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (value : Prefix (Representatives s.key) s.input.r → Truncated (q.p.model.O q.p.t) q.J)
    (event : Event s.key s.input.r) (before after : Cursor s.key s.input.r)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (step : Step s.key s.input.r event before after)
    (ha : Rel s F q node H high E U P before acc a)
    (hnoleaf : ∀ ancestors,event≠Event.leaf ancestors) :
    a.regs controllerPorts.active=true ∧ ∃ steps b,
      Iteration controllerPorts routines steps a b ∧
      Rel s F q node H high E U P after (acc+callbackWeight s.key s.input.r value event) b ∧
      steps+1 ≤ costWeight s.key s.input.r (eventPolynomial s F) leafCost event ∧
      ∀ p z,p ≤ steps+1 → Trace (compiled (body controllerPorts routines) 0 0) p
        (a.withPC (some (compiled (body controllerPorts routines) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ prefixEnvelope s F := by
  obtain ⟨hactive,steps,b,he,hbound,ht,hspace,hframe⟩ :=
    nonleaf_step s F leafCost cap event before after a step ha.boundary hnoleaf
  have hquery := ha.query.frame (query_frame_of_persistent a b hframe)
  have hpair := ha.accumulator.frame (hframe 851 ⟨by decide,by decide,by decide⟩)
  have hz : callbackWeight s.key s.input.r value event=0 := by
    cases event with
    | candidate => rfl
    | exhausted => rfl
    | leaf ancestors => exact False.elim (hnoleaf ancestors rfl)
  refine ⟨hactive,steps,b,he,?_,ht,hspace⟩
  rw [hz,add_zero]
  exact ⟨hbound,hquery,hpair⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.nonleaf_rel_step_oai
