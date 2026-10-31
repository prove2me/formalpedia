-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.setup_rel_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:58:03.736974+00:00
-- url     : https://prove2.me/submissions/a0bb0bd7-9b96-4e1e-b653-e02047c9b21b

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_result_headsize
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleLoader_setup_native_run
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_Counters
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters

open BitProgram CounterPrograms CounterForPrograms

theorem powerTwo_value (width : ℕ) :
    value (List.replicate width false ++ [true]) = 2 ^ width := by
  induction width with
  | zero => rfl
  | succ width ih => simp [List.replicate_succ, ih, pow_succ, Nat.mul_comm]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Counters
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSetupFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Frame and value rules for the actual setup copy/cleanup routines. -/

namespace SubexponentialSAT.SubexpSetupStorage

open BitProgram StructuredCalls

theorem prepare_frame {S : ℕ} (tmp : Fin S) (ports : List (Fin S))
    (inputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (ht : i ≠ tmp) (hp : i ∉ ports) (hi : ∀ p ∈ inputs, i ≠ p.2) :
    (prepareState tmp ports inputs a).stacks i = a.stacks i := by
  unfold prepareState beforeCopies
  rw [copyMany_frame _ _ _ hi, resetMany_stacks, clearMany_stacks,
    ite_eq_right hp, clearMany_stacks]
  simp [ht]

theorem finish_frame {S : ℕ} (ports : List (Fin S))
    (outputs : List (Fin S × Fin S)) (a : Data S) (i : Fin S)
    (hp : i ∉ ports) (ho : ∀ p ∈ outputs, i ≠ p.2) :
    (finishState ports outputs a).stacks i = a.stacks i := by
  have hmem : i ∉ outputs.map Prod.snd := by
    intro hi
    obtain ⟨p, hm, he⟩ := List.mem_map.mp hi
    exact ho p hm he.symm
  unfold finishState
  rw [resetMany_stacks, clearMany_stacks, ite_eq_right hp,
    copyMany_frame _ _ _ ho, clearMany_stacks, ite_eq_right hmem]

end SubexponentialSAT.SubexpSetupStorage

end OAI.Algorithms
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

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

/-- Empty heads are initialized with the sole empty assignment and fuel one. -/
theorem resetState_words (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = []) :
    (resetState a).stacks (tupleStacks 2) = List.replicate h false ∧
      (resetState a).stacks (tupleStacks 7) = List.replicate h false ++ [true] ∧
      (resetState a).stacks (tupleStacks 4) = [] := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  have hbsource : b.stacks 651 = List.replicate h false := by
    have hne : (651 : Fin 896) ≠ tupleStacks 2 := by decide
    simpa [b, copyState, StackRoutines.copyStacks, hne] using hw
  have hcpayload : c.stacks (tupleStacks 4) = List.replicate h false := by
    change b.stacks 651 ++ b.stacks (tupleStacks 4) = _
    rw [hbsource]
    have hp' : b.stacks (tupleStacks 4) = [] := by
      simpa [b, copyState, StackRoutines.copyStacks] using hp
    simp only [hp', List.append_nil]
  have hccandidate : c.stacks (tupleStacks 2) = List.replicate h false := by
    simp [c, b, copyState, StackRoutines.copyStacks, hc, hw]
  constructor
  · change (initialFuelState c).stacks (tupleStacks 2) = _
    unfold initialFuelState
    rw [CounterForPrograms.install_other_stack initialFuelPorts c _ _ _ _ _
      (tupleStacks 2) (by decide) (by decide)]
    exact hccandidate
  constructor
  · change (CounterForPrograms.install initialFuelPorts c _ _ _ _ _).stacks
      initialFuelPorts.scratch = _
    rw [CounterForPrograms.install_scratch]
    change List.replicate (c.stacks (tupleStacks 4)).length false ++ [true] = _
    simp only [hcpayload, List.length_replicate]
  · exact CounterForPrograms.install_counter initialFuelPorts c _ _ _ _ _

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

theorem resetState_assignment (a : State 40 896) (h : ℕ)
    (hw : a.stacks 651 = List.replicate h false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = []) :
    (resetState a).stacks (tupleStacks 2) = ExecCNFTupleEnumeration.fixedBits h 0 := by
  rw [(resetState_words a h hw hc hp).1]
  exact ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
    (by simp [ExecCNFTupleEnumeration.fixedBits_value h 0 (Nat.pow_pos (by decide))])

theorem resetState_source (a : State 40 896) :
    (resetState a).stacks 651 = a.stacks 651 := by
  let b := copyState 651 (tupleStacks 2) a
  let c := copyState 651 (tupleStacks 4) b
  change (initialFuelState c).stacks 651 = a.stacks 651
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts c _ _ _ _ _ 651
    (by decide) (by decide)]
  simp [c, b, copyState, StackRoutines.copyStacks,
    (by decide : (651 : Fin 896) ≠ tupleStacks 2),
    (by decide : (651 : Fin 896) ≠ tupleStacks 4)]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Paid, isolated service calls in the leaf head-builder's reserved bank.
The entire local service bank is moved to340..627. In particular a matrix
entry bank cannot overwrite the persistent ring tables below340. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem protected_ne_work {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) (j : Fin s) : i ≠ workPort hs j := by
  intro h
  have := congrArg Fin.val h
  have := j.isLt
  simp only [workPort] at *
  rcases hi.1 with h | h <;> omega

theorem protected_not_workPorts {s : ℕ} (hs : s ≤ 288) {i : Fin 768}
    (hi : Protected i) : i ∉ workPorts hs := by
  simp only [workPorts,List.mem_ofFn,not_exists]
  intro j h
  exact protected_ne_work hs hi j h.symm

theorem prepared_frame {s : ℕ} (hs : s ≤ 288) (ins : List (Fin 768 × Fin s))
    (a : Data) (i : Fin 768) (hi : Protected i) : (prepared hs ins a).stacks i = a.stacks i := by
  apply prepare_frame _ _ _ _ _ hi.2 (protected_not_workPorts hs hi)
  intro p hp
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
  exact protected_ne_work hs hi q.2

theorem returned_frame {r s : ℕ} (reg : Fin r → Fin 16) (hs : s ≤ 288)
    (ins : List (Fin 768 × Fin s)) (outs : List (Fin s × Fin 768))
    (a : Data) (b : State r s) (i : Fin 768) (hi : Protected i)
    (hn : ∀ p ∈ outs,i≠p.2) : (returned reg hs ins outs a b).stacks i=a.stacks i := by
  have hno : ∀ p ∈ outputCopies hs outs,i≠p.2 := by
    intro p hp
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
    exact hn q hq
  exact (finish_frame _ _ _ _ (protected_not_workPorts hs hi) hno).trans
    ((embedState_stack_frame _ _ _ _ _ (by
      rintro ⟨j,hj⟩; exact protected_ne_work hs hi j hj.symm)).trans
      (prepared_frame hs ins a i hi))

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSelection
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual original/factor ID selection from the common full word table.
The input masters are copied into an isolated lookup program, and its output
records are copied back before the entire lookup workspace is cleared. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem headResult_frame (a : Data) (n : ℕ) (rows : List (List Bool)) (low : List Bool) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h650 : i≠650) (h651 : i≠651) :
    (headResult a n rows low W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) headInputs headOutputs a _ i hi
  intro p hp
  simp only [headOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl <;> assumption

theorem factorResult_frame (a : Data) (A N : ℕ) (rows : List (List Bool)) (W z : ℕ)
    (i : Fin 768) (hi : Protected i) (h671 : i≠671) :
    (factorResult a A N rows W z).stacks i=a.stacks i := by
  apply returned_frame id (by decide) factorInputs factorOutputs a _ i hi
  intro p hp
  simp only [factorOutputs,List.mem_singleton] at hp
  subst p
  exact h671

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Construct the full ambient head-support mask from the IDs actually
selected. A low-variable mask alone is not a head-support mask. -/
noncomputable section

namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem countResult_frame (a : Data) (i : Fin 768) (hi : Protected i) (h652 : i≠652) :
    (countResult a).stacks i=a.stacks i := by
  apply returned_frame countRegs (by decide) countInputs countOutputs a _ i hi
  intro p hp
  simp only [countOutputs,List.mem_singleton] at hp
  subst p
  exact h652

theorem scatterResult_frame (a : Data) (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ)
    (i : Fin 768) (hi : Protected i) (h670 : i≠670) :
    (scatterResult a regs n js).stacks i=a.stacks i := by
  apply returned_frame scatterRegs (by decide) scatterInputs scatterOutputs a _ i hi
  intro p hp
  simp only [scatterOutputs,List.mem_singleton] at hp
  subst p
  exact h670

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The complete head-selection stage. All three objects consumed by the
matrix/bucket phase are computed from runtime masters by fixed programs. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem preparedHead_frame (a : Data) (regs : Fin 8 → Bool) (n N : ℕ)
    (rows : List (List Bool)) (low : List Bool) (W z : ℕ) (i : Fin 768)
    (hi : Protected i) (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h670 : i≠670) (h671 : i≠671) :
    (preparedHead a regs n N rows low W z).stacks i=a.stacks i := by
  rw [preparedHead,factorResult_frame _ _ _ _ _ _ _ hi h671,
    scatterResult_frame _ _ _ _ _ hi h670,countResult_frame _ _ hi h652]
  exact headResult_frame _ _ _ _ _ _ _ hi h650 h651

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

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

/-- Every persistent protected source except the head outputs and matrix
output668 is retained by the local loader. -/
theorem localResult_frame (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (hi : Protected i)
    (h650 : i≠650) (h651 : i≠651) (h652 : i≠652) (h668 : i≠668)
    (h669 : i≠669) (h670 : i≠670) (h671 : i≠671) :
    (localResult a rp rm rs n N W z rows low raw shifted).stacks i=a.stacks i := by
  unfold localResult
  simp only [clearState,Function.update_of_ne h669]
  rw [returned_frame shiftRegs (by decide) shiftInputs shiftOutputs _ _ i hi
    (by simpa [shiftOutputs] using h668)]
  rw [returned_frame id (by decide) matrixInputs rawOutputs _ _ i hi
    (by simpa [rawOutputs] using h669)]
  exact preparedHead_frame a rp n N rows low W z i hi h650 h651 h652 h670 h671

theorem localResult_masters (a : Data) (rp : Fin 8 → Bool) (rm : Fin 16 → Bool)
    (rs : Fin 8 → Bool) (n N W z : ℕ) (rows : List (List Bool)) (low : List Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    MasterFrame a (localResult a rp rm rs n N W z rows low raw shifted) := by
  constructor
  intro i hi
  simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals
    exact localResult_frame a rp rm rs n N W z rows low raw shifted _
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem exportedState_raw (a : State 16 896) : (exportedState a).stacks 846=[] := by
  simp [exportedState,clearMany_stacks]

theorem exportedState_frame (a : State 16 896) (i : Fin 896)
    (hi : i≠659 ∧ i≠668 ∧ i≠669 ∧ i≠846 ∧ i≠847) :
    (exportedState a).stacks i=a.stacks i := by
  simp only [exportedState,clearMany_stacks,List.mem_cons,
    List.not_mem_nil,hi.2.1,hi.2.2.1,hi.2.2.2.1,or_self]
  rw [copyState_frame _ _ _ _ hi.2.2.2.2]
  simp [clearState,hi.1]

theorem addressStateFrom_value (src : Fin 896) (a : State 16 896)
    (hs : src∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks 649=a.stacks src := by
  simp only [addressStateFrom,copyState,StackRoutines.copyStacks,Function.update_self,
    clearMany_stacks, hs, show (649:Fin 896)∈[649,659,846,847] by decide,
    ite_false, ite_true, if_true, List.append_nil]

theorem addressStateFrom_frame (src : Fin 896) (a : State 16 896) (i : Fin 896)
    (hi : i∉([649,659,846,847] : List (Fin 896))) :
    (addressStateFrom src a).stacks i=a.stacks i := by
  have h649 : i≠649 := by intro h; subst i; simp at hi
  rw [addressStateFrom,copyState_frame _ _ _ _ h649,clearMany_stacks]
  simp only [hi, ite_false]

theorem lowResultFrom_low (src : Fin 896) (a : State 16 896) (b : Data) (i : Fin 768)
    (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (exportedState (lowResultFrom src a b)).stacks (lowStacks i)=b.stacks i := by
  have hlow (j : Fin 768) (hj : i≠j) : lowStacks i≠lowStacks j :=
    fun h => hj (lowStacks.injective h)
  have hhigh (j : Fin 896) (hj : 768 ≤ j.val) : lowStacks i≠j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val=j.val at hv
    have := i.isLt
    omega
  rw [exportedState_frame _ _ ⟨hlow 659 h659,hlow 668 h668,hlow 669 h669,
    hhigh 846 (by decide),hhigh 847 (by decide)⟩]
  exact embedState_stack id lowStacks _ b lowStacks.injective i


theorem lowResultFrom_frame (src : Fin 896) (a : State 16 896) (b : Data)
    (i : Fin 896) (hhigh : 768 ≤ i.val)
    (hi : i∉([846,847] : List (Fin 896))) :
    (exportedState (lowResultFrom src a b)).stacks i=a.stacks i := by
  have hn (j : Fin 896) (hj : j.val<768) : i≠j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h846 : i≠846 := by intro h; subst i; simp at hi
  have h847 : i≠847 := by intro h; subst i; simp at hi
  rw [exportedState_frame _ i ⟨hn 659 (by decide),hn 668 (by decide),
    hn 669 (by decide),h846,h847⟩]
  unfold lowResultFrom
  rw [embedState_stack_frame id lowStacks _ b i (by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val=i.val at hv
    have := j.isLt
    omega)]
  apply addressStateFrom_frame
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
  exact ⟨hn 649 (by decide),hn 659 (by decide),h846,h847⟩


theorem leafInputFrom_masters (src : Fin 896) (frame : State 40 896) (base : Data)
    (hf : MasterFrame base (projectState leafRegs lowStacks frame)) :
    MasterFrame base (leafInputFrom src frame) := by
  constructor
  intro i hi
  have hnot : lowStacks i∉([649,659,846,847] : List (Fin 896)) := by
    simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (addressStateFrom_frame src (projectState leafRegs id frame) (lowStacks i) hnot).trans
    (hf.stored i hi)

/-- Retained source equality composes between concrete call boundaries. -/
theorem MasterFrame.trans {a b c : Data} (hab : MasterFrame a b) (hbc : MasterFrame b c) :
    MasterFrame a c := ⟨fun i hi => (hbc.stored i hi).trans (hab.stored i hi)⟩

theorem leafOutputFrom_masters (src : Fin 896) (frame : State 40 896) (base b : Data)
    (hf : MasterFrame base b) :
    MasterFrame base (projectState leafRegs lowStacks (leafOutputFrom src frame b)) := by
  constructor
  intro i hi
  have hne : i≠659 ∧ i≠668 ∧ i≠669 := by
    simp only [masters,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  exact (embedState_stack leafRegs id frame _ Function.injective_id (lowStacks i)).trans
    ((lowResultFrom_low src (projectState leafRegs id frame) b i hne.1 hne.2.1 hne.2.2).trans
      (hf.stored i hi))

/-- The fixed16-register loader leaves every higher caller register intact. -/
theorem leafOutputFrom_registers (src : Fin 896) (frame : State 40 896) (b : Data)
    (i : Fin 40) (hi : 16 ≤ i.val) :
    (leafOutputFrom src frame b).regs i=frame.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hv := congrArg Fin.val hj
  change j.val=i.val at hv
  have := j.isLt
  omega


theorem leafOutputFrom_raw_empty (src : Fin 896) (frame : State 40 896) (b : Data) :
    (leafOutputFrom src frame b).stacks 846=[] :=
  (embedState_stack leafRegs id frame _ Function.injective_id 846).trans (exportedState_raw _)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramRetain
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserve the paid interpolation cache for the later source-polynomial
worker. These three copies are charged before the private head bank is cleared. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

theorem retainedState_frame (a : Data) (i : Fin 768)
    (h659 : i≠659) (h710 : i≠710) (h711 : i≠711) (h712 : i≠712) :
    (retainedState a).stacks i=a.stacks i := by
  rw [retainedState,copyMany_frame]
  · simp [clearMany_stacks,retainedPorts,h659]
  · simp [retainedCopies,h710,h711,h712]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramBootRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact state and cost of the paid per-node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog
namespace LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem addressState_frame (a : Data) (regs : Fin 3 → Bool) (r t : ℕ) (i : Fin 768)
    (hi : Protected i) (h648 : i≠648) (h649 : i≠649) :
    (addressState a regs r t).stacks i=a.stacks i := by
  apply returned_frame addressRegs (by decide) addressInputs addressOutputs a _ i hi
  intro p hp
  simp only [addressOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl
  · exact h648
  · exact h649

theorem countedState_frame (a : Data) (regs : Fin 8 → Bool) (records : List (List Bool))
    (i : Fin 768) (hi : Protected i) (h647 : i≠647) :
    (countedState a regs records).stacks i=a.stacks i := by
  apply returned_frame rowCountRegs (by decide) rowCountInputs rowCountOutputs a _ i hi
  intro p hp
  simp only [rowCountOutputs,List.mem_singleton] at hp
  subst p
  exact h647

theorem bootState_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649] : List (Fin 768))) :
    (bootState a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  rcases hne with ⟨h640,h641,h642,h643,h647,h648,h649⟩
  rw [bootState,returned_frame cacheRegs (by decide) cacheInputs cacheOutputs _ _ i hi,
    countedState_frame _ _ _ _ hi h647,addressState_frame _ _ _ _ _ hi h648 h649]
  intro p hp
  simp only [cacheOutputs,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact h640
  · exact h641
  · exact h642
  · exact h643

end LeafHeadSetupProgram

end SqrtLog

end SubexponentialSAT

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramInitialize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Initialization of one node's physical Cartesian head loop. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem nodeStart_frame (a : Data) (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (r t : ℕ)
    (records : List (List Bool)) (height R width : List Bool) (words : List (List Bool))
    (i : Fin 768) (hi : Protected i)
    (hne : i∉([640,641,642,643,647,648,649,660,665,710,711,712] : List (Fin 768))) :
    (nodeStart a ra rd rc r t records height R width words).stacks i=a.stacks i := by
  have h659 : i≠659 := hi.2
  simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hne
  obtain ⟨h640,h641,h642,h643,h647,h648,h649,h660,h665,h710,h711,h712⟩ := hne
  simp only [nodeStart,tupleInitialized,Function.update_of_ne h665,Function.update_of_ne h660]
  rw [retainedState_frame _ i h659 h710 h711 h712]
  apply bootState_frame a ra rd rc r t records height R width words i hi
  simp [h640,h641,h642,h643,h647,h648,h649]

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end
end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadSetupProgramNativeCache
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The native entry cache is the actual output of the paid node bootstrap. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp
open RowSelectionProgram

theorem start_low (s : Inputs) (a : LeafHeadSetupProgram.Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (i : Fin 768) (hi : i.val < 340) : (start s a ra rd rc words).stacks i=a.stacks i := by
  apply nodeStart_frame
  · constructor
    · left; exact hi
    · intro h; have hh := congrArg Fin.val h; simp [temporary] at hh; omega
  · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
    omega

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram.Native

end

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureHeadLoader
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The concrete head-loader is specialized to actual node bootstrap data.
All physical entry contracts are discharged by the native cache producer. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

/-- The physical shift word is retained exactly from the source bank. Its
word-length cap can therefore be fixed independently of the caller frame. -/
theorem native_offset_word (s : Native.Inputs) (a : Data)
    (ra : Fin 3 → Bool) (rd rc : Fin 8 → Bool) (words : List (List Bool))
    (b : Data) (hf : MasterFrame (Native.start s a ra rd rc words) b) :
    b.stacks 141=a.stacks 141 :=
  (hf.stored 141 (by decide)).trans (Native.start_low s a ra rd rc words 141 (by decide))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureHeadLoader
end
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

theorem initializeLevels_eval (a : State 40 896) (hs : a.stacks (tupleStacks 5) = []) :
    Eval initializeLevelsCommand
      (7 * (a.stacks 130).length + 7 * (a.stacks 649).length + 13)
      a (initializeLevelsState a) := by
  let b := copyState 130 (tupleStacks 6) a
  have hb := copyWord_eval 130 (tupleStacks 6) (tupleStacks 5)
    (by decide) (by decide) (by decide) a hs
  have hbs : b.stacks (tupleStacks 5) = [] := by
    simpa [b, copyState, StackRoutines.copyStacks] using hs
  have hc := copyWord_eval 649 (tupleStacks 9) (tupleStacks 5)
    (by decide) (by decide) (by decide) b hbs
  have ht := Eval.seq hb (Eval.seq hc
    (Eval.base (StructuredProgram.Eval.seq (.atom (.peek (tupleStacks 6) 0 1) _)
      (.seq (.atom (.bnot controllerPorts.leaf 1) _)
        (.atom (.set controllerPorts.active true) _)))))
  have hw : b.stacks 649 = a.stacks 649 := by
    simp [b, copyState, StackRoutines.copyStacks, (by decide : (649 : Fin 896) ≠ tupleStacks 6)]
  rw [hw] at ht
  change Eval initializeLevelsCommand _ a (initializeLevelsState a) at ht
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  omega

theorem initializeLevelsState_words (a : State 40 896) (heads address : ℕ)
    (hh : a.stacks 130 = List.replicate heads true)
    (ha : a.stacks 649 = List.replicate address true)
    (he : a.stacks (tupleStacks 6) = []) (hz : a.stacks (tupleStacks 9) = []) :
    (initializeLevelsState a).stacks (tupleStacks 6) = List.replicate heads true ∧
      (initializeLevelsState a).stacks (tupleStacks 9) = List.replicate address true := by
  change (copyState 649 (tupleStacks 9) (copyState 130 (tupleStacks 6) a)).stacks
      (tupleStacks 6) = _ ∧
    (copyState 649 (tupleStacks 9) (copyState 130 (tupleStacks 6) a)).stacks
      (tupleStacks 9) = _
  simp [copyState, StackRoutines.copyStacks, hh, ha, he, hz,
    (by decide : tupleStacks 6 ≠ tupleStacks 9),
    (by decide : tupleStacks 9 ≠ tupleStacks 6),
    (by decide : (649 : Fin 896) ≠ tupleStacks 6)]

theorem initializeLevelsState_flags (a : State 40 896) (heads : ℕ)
    (hh : a.stacks 130 = List.replicate heads true)
    (he : a.stacks (tupleStacks 6) = []) :
    (initializeLevelsState a).regs controllerPorts.active = true ∧
      (initializeLevelsState a).regs controllerPorts.leaf = decide (heads = 0) := by
  cases heads <;>
    simp [initializeLevelsState, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs,
      copyState, StackRoutines.copyStacks, controllerPorts, hh, he, List.replicate_succ,
      (by decide : tupleStacks 6 ≠ tupleStacks 9)]

theorem initial_remaining_word (h : ℕ) :
    List.replicate h false ++ [true] =
      ExecCNFTupleEnumeration.fixedBits (h + 1) (2 ^ h) := by
  have hp : 0 < 2 ^ h := Nat.pow_pos (by decide)
  have hb : 2 ^ h < 2 ^ (h + 1) := by rw [pow_succ]; omega
  exact ExecCNFTupleEnumeration.word_eq_of_length_value (by simp)
    (by rw [Counters.powerTwo_value, ExecCNFTupleEnumeration.fixedBits_value _ _ hb])

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleNative
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


theorem counter_install_register_frame (p : CounterForPrograms.Ports 40 896)
    (a : State 40 896) (b present flag : Bool) (xs ys : List Bool) (j : Fin 40)
    (hj : ¬ ∃ i, p.register i = j) :
    (CounterForPrograms.install p a b present flag xs ys).regs j = a.regs j :=
  embedState_register_frame _ _ _ _ _ hj

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

theorem initialClearState_tuple (a : State 40 896) (i : Fin 12) :
    (initialClearState a).stacks (tupleStacks i) = [] := by
  rw [initialClearState, clearWordsState_stacks,
    ite_eq_left (List.mem_ofFn.mpr ⟨i, rfl⟩)]

theorem initialClearState_source130 (a : State 40 896) :
    (initialClearState a).stacks 130 = a.stacks 130 := by
  rw [initialClearState, clearWordsState_stacks, ite_eq_right (by decide)]

theorem initialClearState_source649 (a : State 40 896) :
    (initialClearState a).stacks 649 = a.stacks 649 := by
  rw [initialClearState, clearWordsState_stacks, ite_eq_right (by decide)]

theorem initialControlState_tuple (a : State 40 896) (i : Fin 12)
    (h6 : i ≠ 6) (h9 : i ≠ 9) :
    (initialControlState a).stacks (tupleStacks i) = [] := by
  have he6 : tupleStacks i ≠ tupleStacks 6 := fun he => h6 (tupleStacks.injective he)
  have he9 : tupleStacks i ≠ tupleStacks 9 := fun he => h9 (tupleStacks.injective he)
  change (copyState 649 (tupleStacks 9)
    (copyState 130 (tupleStacks 6) (initialClearState a))).stacks (tupleStacks i) = []
  simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne he9, Function.update_of_ne he6]
  exact initialClearState_tuple a i

theorem initialControlState_flags (a : State 40 896) (levels : ℕ)
    (hh : a.stacks 130 = List.replicate levels true) :
    (initialControlState a).regs controllerPorts.active = true ∧
      (initialControlState a).regs controllerPorts.leaf = decide (levels = 0) :=
  initializeLevelsState_flags (initialClearState a) levels
    ((initialClearState_source130 a).trans hh) (initialClearState_tuple a 6)

/-- A zero-head instance enters the single empty-tuple callback; it does not
halt early or skip its neutral group product. -/
theorem setup_zero_eval (loadHead : Cmd 40 896) (a : State 40 896) (base : ℕ)
    (hh : a.stacks 130 = []) (hz : a.stacks 649 = List.replicate base true) :
    Eval (setupWith loadHead)
      (clearWordsTime (List.ofFn tupleStacks) a + 7 * base + 14) a (initialControlState a) := by
  have hi := initializeLevels_eval (initialClearState a) (initialClearState_tuple a 5)
  rw [initialClearState_source130, initialClearState_source649, hh, hz] at hi
  simp only [List.length_nil, List.length_replicate, Nat.mul_zero, Nat.zero_add] at hi
  have hleaf := (initialControlState_flags a 0 hh).2
  have hbranch : Eval (.ite controllerPorts.leaf (.base .skip)
      (.seq loadHead resetGeneratorCommand)) 1 (initialControlState a) (initialControlState a) :=
    .ite_true hleaf (.base (.skip _))
  have he := (clearWords_eval (List.ofFn tupleStacks) a).seq (hi.seq hbranch)
  simpa only [setupWith, initialClearState, initialControlState, Nat.add_assoc] using he

section InitialStorage

variable (h : ℕ → ℕ) {κ : ℕ → Type*}
  (key : (d : ℕ) → Fin (2 ^ h d) → κ d)

theorem initial_ancestor_storage (levels base : ℕ)
    (ancestors : Prefix (Representatives key) 0) (a : State 40 896)
    (hh : a.stacks 130 = List.replicate levels true)
    (hz : a.stacks 649 = List.replicate base true) :
    AncestorStorage h key levels base 0 ancestors (initialControlState a) := by
  have hw := initializeLevelsState_words (initialClearState a) levels base
    ((initialClearState_source130 a).trans hh) ((initialClearState_source649 a).trans hz)
    (initialClearState_tuple a 6) (initialClearState_tuple a 9)
  refine ⟨Nat.zero_le _, ?_, ?_, ?_, ?_, (initialControlState_flags a levels hh).1⟩
  · rw [initialControlState_tuple _ _ (by decide) (by decide)]
    simp [cursorFrames]
  · rw [initialControlState_tuple _ _ (by decide) (by decide)]
    simp [representativeFrames, representativeWords, suspendedFrames]
  · simpa only [initialControlState, Nat.sub_zero] using hw.1
  · simpa only [initialControlState, Nat.add_zero] using hw.2

theorem initial_leaf_storage (base : ℕ)
    (ancestors : Prefix (Representatives key) 0) (a : State 40 896)
    (hh : a.stacks 130 = []) (hz : a.stacks 649 = List.replicate base true) :
    LeafStorage h key 0 base ancestors (initialControlState a) := by
  refine ⟨initial_ancestor_storage h key 0 base ancestors a hh hz,
    (initialControlState_flags a 0 hh).2, ?_⟩
  intro i hi
  simp only [currentHeadPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact initialControlState_tuple a _ (by decide) (by decide)

end InitialStorage


theorem resetState_outside (a : State 40 896) (i : Fin 896)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7) :
    (resetState a).stacks i = a.stacks i := by
  change (initialFuelState (copyState 651 (tupleStacks 4)
    (copyState 651 (tupleStacks 2) a))).stacks i = a.stacks i
  unfold initialFuelState
  rw [CounterForPrograms.install_other_stack initialFuelPorts _ _ _ _ _ _ i h4 h7]
  simp only [copyState, StackRoutines.copyStacks, Function.update_of_ne h4, Function.update_of_ne h2]

theorem resetGeneratorState_outside (a : State 40 896) (i : Fin 896)
    (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4) (h7 : i ≠ tupleStacks 7)
    (h8 : i ≠ tupleStacks 8) :
    (resetGeneratorState a).stacks i = a.stacks i := by
  change Function.update (resetState a).stacks (tupleStacks 8)
    ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) i = a.stacks i
  rw [Function.update_of_ne h8, resetState_outside a i h2 h4 h7]

theorem resetGeneratorState_cursor (a : State 40 896) (width : ℕ)
    (hh : a.stacks 651 = List.replicate width false)
    (hc : a.stacks (tupleStacks 2) = []) (hp : a.stacks (tupleStacks 4) = [])
    (ht : a.stacks (tupleStacks 5) = []) (hi : a.stacks (tupleStacks 10) = []) :
    CursorWords (resetGeneratorState a) width 0 := by
  have hwords := resetState_words a width hh hc hp
  have hcandidate : (resetGeneratorState a).stacks candidatePorts.counter =
      ExecCNFTupleEnumeration.fixedBits width 0 := by
    change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) candidatePorts.counter = _
    rw [Function.update_of_ne (by decide)]
    exact resetState_assignment a width hh hc hp
  have hremaining : (resetGeneratorState a).stacks remainingPorts.counter =
      ExecCNFTupleEnumeration.fixedBits (width + 1) (2 ^ width) := by
    change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) remainingPorts.counter = _
    rw [Function.update_of_ne (by decide)]
    exact hwords.2.1.trans (initial_remaining_word width)
  refine ⟨Nat.zero_le _, ?_, ?_, fun _ => hcandidate, ?_, ?_, ?_⟩
  · rw [hcandidate, ExecCNFTupleEnumeration.fixedBits_value _ _ (Nat.pow_pos (by decide))]
  · rw [hcandidate, ExecCNFTupleEnumeration.fixedBits_length]
    omega
  · simpa using hremaining
  · rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
    exact hi
  · rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
    exact ht

theorem resetGeneratorState_predecessor (a : State 40 896) (width : ℕ)
    (hh : a.stacks 651 = List.replicate width false)
    (hp : a.stacks (tupleStacks 8) = []) :
    (resetGeneratorState a).stacks (tupleStacks 8) = List.replicate width false := by
  change Function.update (resetState a).stacks (tupleStacks 8)
    ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 8) = _
  rw [Function.update_self, resetState_source,
    resetState_outside _ _ (by decide) (by decide) (by decide), hh, hp, List.append_nil]

theorem resetGeneratorState_register_frame (a : State 40 896) (j : Fin 40)
    (hj : 3 ≤ j.val) (hav : j ≠ controllerPorts.available)
    (hfresh : j ≠ controllerPorts.fresh) :
    (resetGeneratorState a).regs j = a.regs j := by
  have h0 : j ≠ 0 := by intro he; subst j; norm_num at hj
  have h1 : j ≠ 1 := by intro he; subst j; norm_num at hj
  change readRegs (resetState a).regs 0 1 none j = a.regs j
  rw [StackRoutines.readRegs_frame _ _ _ _ _ h0 h1]
  unfold resetState
  simp only [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, execInstr,
    Function.update_of_ne hfresh, Function.update_of_ne hav]
  unfold initialFuelState
  rw [counter_install_register_frame _ _ _ _ _ _ _ j ?_]
  · exact (StackRoutines.readRegs_frame _ _ _ _ _ h0 h1).trans
      (StackRoutines.readRegs_frame _ _ _ _ _ h0 h1)
  · rintro ⟨i, hi⟩
    have hv := congrArg Fin.val hi
    have hil := i.isLt
    change i.val = j.val at hv
    omega

/-- Reset follows a real matrix load. It preserves the attained ancestor
frames and prepares exactly the first numeric assignment for this head. -/
theorem reset_scan_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2 ^ h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val) (a : State 40 896)
    (ha : AncestorStorage h key levels base depth.val ancestors a)
    (hl : a.regs controllerPorts.leaf = false)
    (hh : a.stacks 651 = List.replicate (h depth.val) false)
    (hc : a.stacks (tupleStacks 2) = []) (hk : a.stacks (tupleStacks 3) = [])
    (hp : a.stacks (tupleStacks 4) = []) (ht : a.stacks (tupleStacks 5) = [])
    (hz : a.stacks (tupleStacks 8) = []) (hi : a.stacks (tupleStacks 10) = []) :
    ScanStorage h key levels base depth ancestors 0 (resetGeneratorState a) := by
  have hf (i : Fin 896) (h2 : i ≠ tupleStacks 2) (h4 : i ≠ tupleStacks 4)
      (h7 : i ≠ tupleStacks 7) (h8 : i ≠ tupleStacks 8) :
      (resetGeneratorState a).stacks i = a.stacks i :=
    resetGeneratorState_outside a i h2 h4 h7 h8
  refine ⟨⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩,
    resetGeneratorState_cursor a (h depth.val) hh hc hp ht hi, ?_, ?_, ?_,
    resetGeneratorState_predecessor a (h depth.val) hh hz⟩
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.cursors
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.representatives
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.heads
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact ha.address
  · rw [resetGeneratorState_register_frame _ _ (by decide) (by decide) (by decide)]
    exact ha.active
  · rw [resetGeneratorState_register_frame _ _ (by decide) (by decide) (by decide)]
    exact hl
  · rw [hf _ (by decide) (by decide) (by decide) (by decide)]; exact hk
  · change Function.update (resetState a).stacks (tupleStacks 8)
      ((resetState a).stacks 651 ++ (resetState a).stacks (tupleStacks 8)) (tupleStacks 4) = []
    rw [Function.update_of_ne (by decide)]
    exact (resetState_words a (h depth.val) hh hc hp).2.2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRefinement
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

theorem result_high_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
    (result s z frame rp rm rs raw shifted).stacks i=frame.stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id i).trans
    (SignatureHeadLoader.lowResultFrom_frame headAddress _ _ i hi hne)

theorem result_register_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 40) (hi : 16 ≤ i.val) :
    (result s z frame rp rm rs raw shifted).regs i=frame.regs i :=
  SignatureHeadLoader.leafOutputFrom_registers headAddress frame _ i hi

theorem result_low (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks i)=
      (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom headAddress frame)
        rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id (SignatureHeadLoader.lowStacks i)).trans
    (SignatureHeadLoader.lowResultFrom_low headAddress _ _ i h659 h668 h669)

theorem result_raw_empty (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 846=[] :=
  SignatureHeadLoader.leafOutputFrom_raw_empty headAddress frame _

/-- The source words and caches retain their exact values across the loader. -/
theorem result_masters (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (base : Data)
    (hf : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks frame)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (result s z frame rp rm rs raw shifted)) := by
  apply SignatureHeadLoader.leafOutputFrom_masters
  exact (SignatureHeadLoader.leafInputFrom_masters headAddress frame base hf).trans
    (SignatureHeadLoader.localResult_masters ..)

section Storage
open SignatureTupleDFS SignatureTupleTraversal

/-- Reloading a head preserves the complete attained ancestor path. -/
theorem result_ancestor_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base depth : ℕ)
    (ancestors : Prefix (Representatives key) depth)
    (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth ancestors frame) :
    AncestorStorage h key levels base depth ancestors
      (result s z frame rp rm rs raw shifted) := by
  refine ⟨ha.depth_le, ?_, ?_, ?_, ?_, ?_⟩
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 0) (by decide) (by decide)]
    exact ha.cursors
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 1) (by decide) (by decide)]
    exact ha.representatives
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 6) (by decide) (by decide)]
    exact ha.heads
  · rw [result_high_frame s z frame rp rm rs raw shifted (tupleStacks 9) (by decide) (by decide)]
    exact ha.address
  · rw [result_register_frame s z frame rp rm rs raw shifted controllerPorts.active (by decide)]
    exact ha.active

/-- A completed reload followed by the actual bounded counter initializer
establishes the next head's concrete scan boundary. -/
theorem result_reset_scan_storage (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (depth : Fin levels)
    (ancestors : Prefix (Representatives key) depth.val)
    (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (ha : AncestorStorage h key levels base depth.val ancestors frame)
    (hl : frame.regs controllerPorts.leaf=false)
    (hh : (selectedHeads s.n s.rows s.low z).length=h depth.val)
    (hc : frame.stacks (tupleStacks 2)=[]) (hk : frame.stacks (tupleStacks 3)=[])
    (hp : frame.stacks (tupleStacks 4)=[]) (ht : frame.stacks (tupleStacks 5)=[])
    (hz : frame.stacks (tupleStacks 8)=[]) :
    ScanStorage h key levels base depth ancestors 0
      (resetGeneratorState (result s z frame rp rm rs raw shifted)) := by
  apply reset_scan_storage h key levels base depth ancestors
  · exact result_ancestor_storage h key levels base depth.val ancestors s z frame rp rm rs raw shifted ha
  · rw [result_register_frame s z frame rp rm rs raw shifted controllerPorts.leaf (by decide)]
    exact hl
  · rw [result_headsize, hh]
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 2)
      (by decide) (by decide)).trans hc
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 3)
      (by decide) (by decide)).trans hk
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 4)
      (by decide) (by decide)).trans hp
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 5)
      (by decide) (by decide)).trans ht
  · exact (result_high_frame s z frame rp rm rs raw shifted (tupleStacks 8)
      (by decide) (by decide)).trans hz
  · exact result_raw_empty ..


theorem initialControlState_outside_tuple (a : State 40 896) (i : Fin 896)
    (hi : ∀ j : Fin 12, i≠tupleStacks j) :
    (initialControlState a).stacks i=a.stacks i := by
  change (SignatureTupleProgram.copyState 649 (tupleStacks 9) (SignatureTupleProgram.copyState 130 (tupleStacks 6)
    (initialClearState a))).stacks i=_
  simp only [SignatureTupleProgram.copyState,StackRoutines.copyStacks,Function.update_of_ne (hi 9),
    Function.update_of_ne (hi 6)]
  rw [initialClearState,clearWordsState_stacks,ite_eq_right]
  intro hm
  obtain ⟨j,hj⟩ := List.mem_ofFn.mp hm
  exact hi j hj.symm

/-- Initializing controller words restores the input cap before the first
matrix loader is invoked. -/
theorem initialControl_endpoint_bound (a : State 40 896) (levels base F : ℕ)
    (hh : a.stacks 130=List.replicate levels true)
    (hz : a.stacks 649=List.replicate base true)
    (hframe : ∀ i, (a.stacks i).length≤F) :
    ∀ i, ((initialControlState a).stacks i).length≤F := by
  have hwords := initializeLevelsState_words (initialClearState a) levels base
    ((initialClearState_source130 a).trans hh) ((initialClearState_source649 a).trans hz)
    (initialClearState_tuple a 6) (initialClearState_tuple a 9)
  have hl := hframe 130
  have hb := hframe 649
  rw [hh,List.length_replicate] at hl
  rw [hz,List.length_replicate] at hb
  intro i
  by_cases hi : ∃ j : Fin 12, i=tupleStacks j
  · obtain ⟨j,rfl⟩ := hi
    by_cases h6 : j=6
    · subst j
      change ((initializeLevelsState (initialClearState a)).stacks (tupleStacks 6)).length≤F
      rw [hwords.1,List.length_replicate]
      exact hl
    by_cases h9 : j=9
    · subst j
      change ((initializeLevelsState (initialClearState a)).stacks (tupleStacks 9)).length≤F
      rw [hwords.2,List.length_replicate]
      exact hb
    rw [initialControlState_tuple a j h6 h9,List.length_nil]
    exact Nat.zero_le _
  · rw [initialControlState_outside_tuple a i (fun j hj => hi ⟨j,hj⟩)]
    exact hframe i


private theorem low_outside_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  have := i.isLt
  omega

theorem initialControl_masters (a : State 40 896) (base : Data)
    (hm : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks
        (initialControlState a)) := by
  constructor
  intro i hi
  exact (initialControlState_outside_tuple a (SignatureHeadLoader.lowStacks i)
    (low_outside_tuple i)).trans (hm.stored i hi)


/-- The native loader leaves its requested physical address on low649.
This is needed when a later pair restarts the same tuple traversal. -/
theorem result_address649 (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (result s z frame rp rm rs raw shifted).stacks 649=frame.stacks headAddress := by
  change (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks 649)=_
  rw [result_low s z frame rp rm rs raw shifted 649 (by decide) (by decide) (by decide)]
  rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ 649
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  exact SignatureHeadLoader.addressStateFrom_value headAddress _ (by decide)

theorem reset_result_address649 (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool))) :
    (resetGeneratorState (result s z frame rp rm rs raw shifted)).stacks 649=frame.stacks headAddress := by
  rw [resetGeneratorState_outside _ _ (by decide) (by decide) (by decide) (by decide)]
  exact result_address649 ..


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

theorem source_offset (s : ProducedSource) (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    a.stacks 141=s.source.stacks 141 :=
  SignatureHeadLoader.native_offset_word s.input s.source s.addressRegisters s.dimensionRegisters
    s.cacheRegisters s.cacheWords _ hm

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

/-- The concrete loader retains every persistent query word, including the
finite-ring caches that are not part of its own eighteen input masters. -/
theorem result_persistent (s : Native.Inputs) (z : ℕ) (a : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : PersistentPort i) :
    (result s z a rp rm rs raw shifted).stacks i=a.stacks i := by
  by_cases hlow : i.val < 768
  · let j : Fin 768 := ⟨i.val,hlow⟩
    have he : i=SignatureHeadLoader.lowStacks j := Fin.ext rfl
    have hne (q : Fin 768)
        (hm : SignatureHeadLoader.lowStacks q∈([649,650,651,652,659,668,669,670,671] : List (Fin 896))) :
        j≠q := by
      intro hj
      apply hi.head
      simpa only [he,hj] using hm
    have hj : Protected j := ⟨hi.outsideWork,hne 659 (by decide)⟩
    rw [he,result_low s z a rp rm rs raw shifted j
      (hne 659 (by decide)) (hne 668 (by decide))
      (hne 669 (by decide))]
    rw [SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ j hj
      (hne 650 (by decide)) (hne 651 (by decide))
      (hne 652 (by decide)) (hne 668 (by decide))
      (hne 669 (by decide)) (hne 670 (by decide))
      (hne 671 (by decide))]
    have ha : i∉([649,659,846,847] : List (Fin 896)) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨fun h => hi.head (by simp [h]),fun h => hi.head (by simp [h]),hi.tuple 10,hi.tuple 11⟩
    rw [he] at ha
    exact SignatureHeadLoader.addressStateFrom_frame 845 _ (SignatureHeadLoader.lowStacks j) ha
  · apply result_high_frame
    · omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hi.tuple 10,hi.tuple 11⟩

theorem reset_persistent (a : State 40 896) (i : Fin 896) (hi : PersistentPort i) :
    (resetGeneratorState a).stacks i=a.stacks i :=
  resetGeneratorState_outside a i (hi.tuple 2) (hi.tuple 4) (hi.tuple 7) (hi.tuple 8)

private theorem low_not_tuple (i : Fin 768) (j : Fin 12) :
    SignatureHeadLoader.lowStacks i≠tupleStacks j := by
  intro he
  have hv := congrArg Fin.val he
  change i.val=836+j.val at hv
  omega

theorem reset_masters (s : ProducedSource) (a : State 40 896)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a)) :
    SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks (resetGeneratorState a)) := by
  constructor
  intro i hi
  exact (resetGeneratorState_outside a (SignatureHeadLoader.lowStacks i)
    (low_not_tuple i 2) (low_not_tuple i 4) (low_not_tuple i 7) (low_not_tuple i 8)).trans
    (hm.stored i hi)

/-- Positive-depth entry performs paid clearing, the real first head load,
and exact bounded-memory initialization of its assignment cursor. -/
theorem setup_positive (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (a : State 40 896) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649 = unary s.base) (hr : 0 < s.input.r) :
    ∃ n b, Eval (setupWith loadHead) n a b ∧
      Boundary s F (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (setupWith loadHead) 0 0) p
        (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hW := s.source_offset a hm
  obtain ⟨rp,rm,rs,raw,shifted,n,he,ht,hend,hready,hraw,hshift,hspace⟩ :=
    setup_native_run s.input s.source s.ready s.bound s.bounded s.rows s.addressRegisters
      s.dimensionRegisters s.cacheRegisters s.cacheWords s.cache a hm s.base F s.bound hz hr hbound
      (by simpa only [hW] using s.bounded 141) cap.output
  let b := initialControlState a
  let finish := resetGeneratorState (result s.input s.base b rp rm rs raw shifted)
  have hheads : a.stacks 130=unary s.input.r :=
    (hm.stored 130 (by decide)).trans
      ((Native.start_low s.input s.source s.addressRegisters s.dimensionRegisters s.cacheRegisters
        s.cacheWords 130 (by decide)).trans s.ready.colors)
  have hanc := initial_ancestor_storage s.headSize s.key s.input.r s.base (fun i => Fin.elim0 i)
    a hheads hz
  have hleaf : b.regs controllerPorts.leaf=false := by
    rw [(initialControlState_flags a s.input.r hheads).2]
    simp only [Nat.ne_of_gt hr,decide_false]
  have blank (i : Fin 12) (h6 : i≠6) (h9 : i≠9) : b.stacks (tupleStacks i)=[] :=
    initialControlState_tuple a i h6 h9
  have hscan := result_reset_scan_storage s.headSize s.key s.input.r s.base ⟨0,hr⟩
    (fun i => Fin.elim0 i) s.input s.base b rp rm rs raw shifted hanc hleaf
    (by simp only [ProducedSource.headSize,Nat.add_zero])
    (blank 2 (by decide) (by decide)) (blank 3 (by decide) (by decide))
    (blank 4 (by decide) (by decide)) (blank 5 (by decide) (by decide))
    (blank 8 (by decide) (by decide))
  have hnext : ScanBoundary s F ⟨0,hr⟩ (fun i => Fin.elim0 i) 0 finish := by
    refine ⟨hscan,hend,?_,?_,?_⟩
    · apply reset_masters
      exact result_masters s.input s.base b rp rm rs raw shifted s.masters (initialControl_masters a _ hm)
    · constructor
      refine ⟨raw,shifted,?_,?_,?_⟩
      · simpa only [Nat.add_zero] using hraw
      · simpa only [hW] using hshift
      · intro hc
        simpa only [hW,ProducedSource.headSize,Nat.add_zero] using hready
    · rw [reset_result_address649]
      exact hanc.address
  refine ⟨n,finish,he,?_,?_,?_,?_⟩
  · rw [enter_internal s.key s.input.r 0 hr]
    exact Boundary.scan hnext
  · unfold eventPolynomial
    omega
  · intro p q hp hq i
    exact (hspace p q hp hq i).trans (by unfold prefixEnvelope; omega)
  · intro i hi
    rw [reset_persistent _ i hi,result_persistent _ _ _ _ _ _ _ _ i hi]
    exact initialControlState_outside_tuple a i hi.tuple

theorem initial_zero_cursor (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ) (a : State 40 896)
    (hz : levels=0) (hh : a.stacks 130=[]) (ha : a.stacks 649=List.replicate base true) :
    CursorStorage h key levels base
      (enter key levels 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) (initialControlState a) := by
  subst levels
  simpa only [enter_leaf] using
    (CursorStorage.leaf (initial_leaf_storage h key base (fun i => Fin.elim0 i) a hh ha))


/-- With no heads, the real setup reaches one empty-tuple leaf. It preserves
the node base and all query data; the concrete visitor supplies the unit. -/
theorem setup_zero (s : ProducedSource) (F : ℕ) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base) (hr : s.input.r=0) :
    ∃ n b, Eval (setupWith loadHead) n a b ∧
      Boundary s F (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (setupWith loadHead) 0 0) p
        (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  have hheads : a.stacks 130=[] := by
    have hh := (hm.stored 130 (by decide)).trans
      ((Native.start_low s.input s.source s.addressRegisters s.dimensionRegisters s.cacheRegisters
        s.cacheWords 130 (by decide)).trans s.ready.colors)
    change a.stacks (SignatureHeadLoader.lowStacks 130) = unary s.input.r at hh
    have he : SignatureHeadLoader.lowStacks (130 : Fin 768) = (130 : Fin 896) := rfl
    simpa only [he, hr, unary, List.replicate_zero] using hh
  have he := setup_zero_eval loadHead a s.base hheads hz
  have hc := initial_zero_cursor s.headSize s.key s.input.r s.base a hr hheads hz
  have hb := initialControl_endpoint_bound a 0 s.base F hheads hz hbound
  have hnext : Boundary s F
      (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) (initialControlState a) := by
    rw [enter,dite_eq_left hr.symm] at hc ⊢
    cases hc with
    | leaf hl =>
      apply Boundary.leaf
      refine ⟨hl,hb,initialControl_masters a _ hm,?_⟩
      intro _
      exact (initialControlState_outside_tuple a 649 (by decide)).trans hz
  have hclear := clearWordsTime_le_on (List.ofFn tupleStacks) a F (fun i _ => hbound i)
  rw [List.length_ofFn] at hclear
  have hbase : s.base ≤ F := by simpa only [hz,unary,List.length_replicate] using hbound 649
  have ht : clearWordsTime (List.ofFn tupleStacks) a+7*s.base+14+1 ≤ 31*F+51 := by omega
  refine ⟨_,initialControlState a,he,hnext,?_,?_,?_⟩
  · unfold eventPolynomial
    omega
  · have hlocal := StructuredSpace.local_stack_bound (compiled (setupWith loadHead) 0 0)
      (a := a.withPC (some (compiled (setupWith loadHead) 0 0).entry))
      (steps := 31*F+51) (StreamResources.dataBits_le_mul _ hbound)
    intro p q hp hq i
    exact (hlocal p q (by omega) hq i).trans (by unfold prefixEnvelope; omega)
  · intro i hi
    exact initialControlState_outside_tuple a i hi.tuple

/-- Setup for the fixed actual DFS, including its zero-head entry. -/
theorem setup_run (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    (a : State 40 896) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base) :
    ∃ n b, Eval (setupWith loadHead) n a b ∧
      Boundary s F (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) b ∧
      n+1 ≤ eventPolynomial s F ∧
      (∀ p q,p ≤ n+1 → Trace (compiled (setupWith loadHead) 0 0) p
        (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) q →
        ∀ i,(q.stacks i).length ≤ prefixEnvelope s F) ∧
      ∀ i,PersistentPort i → b.stacks i=a.stacks i := by
  by_cases hr : s.input.r=0
  · exact setup_zero s F a hbound hm hz hr
  · exact setup_positive s F cap a hbound hm hz (Nat.pos_of_ne_zero hr)

theorem queryMaster_persistent (i : Fin 896) (hi : i∈QueryTupleState.masterPorts) :
    PersistentPort i := by
  simp only [QueryTupleState.masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact ⟨by decide,by decide,by decide⟩

theorem query_frame_of_persistent (a b : State 40 896)
    (hf : ∀ i,PersistentPort i → b.stacks i=a.stacks i) :
    QueryTupleState.QueryMasterFrame a b :=
  ⟨fun i hi => hf i (queryMaster_persistent i hi)⟩

/-- The actual setup preserves the prepared ring context and the pair
accumulator while installing the first cursor (or the empty tuple leaf). -/
theorem setup_rel_run_oai (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    ∃ steps b, Eval (setupWith loadHead) steps a b ∧
      Rel s F q node H high E U P
        (enter s.key s.input.r 0 (Nat.zero_le _) (fun i => Fin.elim0 i)) acc b ∧
      steps+1 ≤ eventPolynomial s F ∧
      ∀ p z,p ≤ steps+1 → Trace (compiled (setupWith loadHead) 0 0) p
        (a.withPC (some (compiled (setupWith loadHead) 0 0).entry)) z →
        ∀ i,(z.stacks i).length ≤ prefixEnvelope s F := by
  obtain ⟨steps,b,he,hb,ht,hspace,hframe⟩ := setup_run s F cap a hbound hm hz
  exact ⟨steps,b,he,⟨hb,hquery.frame (query_frame_of_persistent a b hframe),
    hacc.frame (hframe 851 ⟨by decide,by decide,by decide⟩)⟩,ht,hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.setup_rel_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete.setup_rel_run_oai
