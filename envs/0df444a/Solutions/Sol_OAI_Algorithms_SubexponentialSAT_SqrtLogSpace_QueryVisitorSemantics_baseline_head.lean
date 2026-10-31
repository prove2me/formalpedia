-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_head
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:50:29.355456+00:00
-- url     : https://prove2.me/submissions/ae7928c4-acc5-4de5-b301-bddfdda9f2ee

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_load_run_polynomial
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_result_mask_count
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_result_mask_length
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_result_mask_word
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorProgram_install_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

open OAI.Algorithms.SubexponentialSAT.StackRoutines

namespace NativeOverlay
open OAI.Algorithms.SubexponentialSAT.StackRoutines

theorem result_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result a rf).stacks i=a.stacks i := by
  by_cases hn : ∃ j, stackMap j=i
  · obtain ⟨j,rfl⟩ := hn
    rw [show (result a rf).stacks (stackMap j)=
      (Overlay.state rf (a.stacks 859) (a.stacks 670)
        (a.stacks 869) (a.stacks 870) (a.stacks 871) [] [] [] [] []
        (LeafAssignmentMergeProgram.merge (Restriction.zeroMerge (a.stacks 670) (a.stacks 859))
          (a.stacks 670) (a.stacks 869)) []).stacks j from
      embedState_stack regMap stackMap a _ (by decide) j]
    fin_cases j <;> simp_all [stackMap,changed,Overlay.state]
  · exact embedState_stack_frame regMap stackMap a _ i hn

theorem reset_frame (a : Data) (i : Fin 896) (hi : i ∉ changed) :
    (resetState a).stacks i = a.stacks i :=
  BankRoutines.clearBankStacks_frame i changed a.stacks hi



@[simp] theorem prepared_assignment (a : Data) (rf : Fin 8 → Bool) :
    (result (resetState a) rf).stacks 145=LeafAssignmentMergeProgram.merge
      (Restriction.zeroMerge (a.stacks 670) (a.stacks 859)) (a.stacks 670) (a.stacks 869) := by
  rw [result_assignment,reset_frame a 670 (by decide),reset_frame a 859 (by decide),
    reset_frame a 869 (by decide)]

theorem prepared_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result (resetState a) rf).stacks i=a.stacks i :=
  (result_frame (resetState a) rf i hi).trans (reset_frame a i hi)

end NativeOverlay


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

theorem overwriteState_frame (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (i : Fin 896) (hi : i ≠ dst) :
    (overwriteState src dst a).stacks i = a.stacks i := by
  rw [overwriteState_stacks src dst hsd,Function.update_of_ne hi]

theorem installedRepresentative_frame (a : Data) (rf : Fin 8 → Bool) (i : Fin 896)
    (hi : i ∉ ([145,859,869,872,873,874,875,876,877] : List (Fin 896))) :
    (installedRepresentative a rf).stacks i = a.stacks i := by
  have h859 : i ≠ 859 := by intro h; subst i; exact hi (by simp)
  have h869 : i ≠ 869 := by intro h; subst i; exact hi (by simp)
  have hover : i ∉ HighQueryAdapter.NativeOverlay.changed := by
    intro h
    simp only [HighQueryAdapter.NativeOverlay.changed,List.mem_cons,
      List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> exact hi (by decide)
  simp only [installedRepresentative,StackRoutines.clearStacks,Function.update_of_ne h859]
  rw [overwriteState_frame _ _ (by decide) _ _ h869,
    overlaidRepresentative,HighQueryAdapter.NativeOverlay.prepared_frame _ _ _ hover,
    stagedRepresentative,overwriteState_frame _ _ (by decide) _ _ h859]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

theorem prefix_local (command : Code) (steps B : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    PrefixBound command steps a (896*B+steps) := by
  constructor
  exact StructuredSpace.local_stack_bound (compiled command 838 838)
    (StreamResources.dataBits_le_mul _ ha)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryRepresentativeFold
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafAssignmentMergeProgram

theorem zeroMerge_length (mask word : List Bool) :
    (HighIncidenceProgram.Restriction.zeroMerge mask word).length = mask.length := by
  induction mask generalizing word with
  | nil => rfl
  | cons b mask ih => cases b <;> simp [HighIncidenceProgram.Restriction.zeroMerge,
      HighIncidenceProgram.Restriction.merge, ih]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryRepresentativeFold
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

namespace QueryMasterFrame

theorem trans {a b c : Data} (hab : QueryMasterFrame a b) (hbc : QueryMasterFrame b c) :
    QueryMasterFrame a c := ⟨fun i hi => (hbc.word i hi).trans (hab.word i hi)⟩

end QueryMasterFrame

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

namespace DenseWord

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {port : Fin 896}
    {value : Dense (q.p.model.O q.p.t) q.p.t q.J} {a b : Data}
    (h : DenseWord q port value a) (hf : b.stacks port=a.stacks port) :
    DenseWord q port value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end DenseWord

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

theorem exportedState_frame (a : State 16 896) (i : Fin 896)
    (hi : i≠659 ∧ i≠668 ∧ i≠669 ∧ i≠846 ∧ i≠847) :
    (exportedState a).stacks i=a.stacks i := by
  simp only [exportedState,clearMany_stacks,List.mem_cons,
    List.not_mem_nil,hi.2.1,hi.2.2.1,hi.2.2.2.1,or_self]
  rw [copyState_frame _ _ _ _ hi.2.2.2.2]
  simp [clearState,hi.1]

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid reverse-head reload for the two-pass query visitor. The same native
run returns every integer row, preserves the suspended query data, and restores
a fixed retained word cap before the next head. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem result_high_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
    (result s z frame rp rm rs raw shifted).stacks i=frame.stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id i).trans
    (SignatureHeadLoader.lowResultFrom_frame 843 _ _ i hi hne)

theorem result_register_frame (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 40) (hi : 16 ≤ i.val) :
    (result s z frame rp rm rs raw shifted).regs i=frame.regs i :=
  SignatureHeadLoader.leafOutputFrom_registers 843 frame _ i hi

theorem result_low (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))
    (i : Fin 768) (h659 : i≠659) (h668 : i≠668) (h669 : i≠669) :
    (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks i)=
      (SignatureHeadLoader.localResult (SignatureHeadLoader.leafInputFrom 843 frame)
        rp rm rs s.n s.N (s.Q*s.r) z s.rows s.low raw shifted).stacks i := by
  exact (embedState_stack SignatureHeadLoader.leafRegs id frame _
    Function.injective_id (SignatureHeadLoader.lowStacks i)).trans
    (SignatureHeadLoader.lowResultFrom_low 843 _ _ i h659 h668 h669)

section Outputs
variable (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))

theorem result_protected_frame (i : Fin 768) (hp : Protected i)
    (hne : i∉([649,650,651,652,659,668,669,670,671] : List (Fin 768))) :
    (result s z frame rp rm rs raw shifted).stacks (SignatureHeadLoader.lowStacks i)=
      frame.stacks (SignatureHeadLoader.lowStacks i) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
  rcases hne with ⟨h649,h650,h651,h652,h659,h668,h669,h670,h671⟩
  rw [result_low s z frame rp rm rs raw shifted i h659 h668 h669,
    SignatureHeadLoader.localResult_frame _ _ _ _ _ _ _ _ _ _ _ _ i hp
      h650 h651 h652 h668 h669 h670 h671]
  apply SignatureHeadLoader.addressStateFrom_frame
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_,?_,?_,?_⟩
  · intro h
    have hv := congrArg (fun j : Fin 896 => j.val) h
    exact h649 (Fin.ext hv)
  · intro h
    have hv := congrArg (fun j : Fin 896 => j.val) h
    exact h659 (Fin.ext hv)
  · intro h
    have hv := congrArg Fin.val h
    change i.val=846 at hv
    have := i.isLt
    omega
  · intro h
    have hv := congrArg Fin.val h
    change i.val=847 at hv
    have := i.isLt
    omega

theorem result_query_master_frame :
    QueryTupleState.QueryMasterFrame frame (result s z frame rp rm rs raw shifted) := by
  constructor
  intro i hi
  simp only [QueryTupleState.masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact result_protected_frame s z frame rp rm rs raw shifted 78 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 128 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 129 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 130 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 131 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 132 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 133 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 134 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 135 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 136 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 138 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 139 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 140 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 141 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 194 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 201 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 202 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 203 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 204 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 207 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 209 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 211 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 212 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 243 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 256 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 280 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 281 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 300 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 301 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 302 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 305 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 307 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 320 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 322 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 338 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 640 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 641 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 642 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 647 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 700 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 701 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 702 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 703 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 704 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 705 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 706 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 707 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 708 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 709 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 710 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 711 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 712 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 713 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 714 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 715 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 716 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 717 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 718 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 719 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 728 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 730 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 731 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 732 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 733 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 734 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 735 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 736 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 737 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 738 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 739 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 740 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 741 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 742 (by decide) (by decide)
  · exact result_protected_frame s z frame rp rm rs raw shifted 743 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 832 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 833 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 834 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 835 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 850 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 857 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 858 (by decide) (by decide)
  · exact result_high_frame s z frame rp rm rs raw shifted 863 (by decide) (by decide)

end Outputs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource

/-- One first-pass visit reloads the real head, then installs its parsed
representative in the ambient baseline. No head-mask producer is assumed. -/
theorem baseline_head_oai {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (s : ProducedSource) (z : ℕ)
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 843=unary z) (htmp : a.stacks 841=[])
    (hword : (a.stacks 838).length=(selectedHeads s.input.n s.input.rows s.input.low z).length)
    (hbase : (a.stacks 869).length=s.input.n)
    (hcap : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
      s.input.columnLength s.bound ≤ B) :
    ∃ steps b, Eval QueryVisitorProgram.baselineHead steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 tupleValue b ∧ QueryMasterFrame a b ∧ WordBound B b ∧
      b.stacks 869=LeafAssignmentMergeProgram.merge
        (HighIncidenceProgram.Restriction.zeroMerge (mask s z) (a.stacks 838))
        (mask s z) (a.stacks 869) ∧ (b.stacks 869).length=s.input.n ∧
      (∀ i : Fin 896,768 ≤ i.val →
        i∉([846,847,859,869,872,873,874,875,876,877] : List (Fin 896)) →
        b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps ≤ baselineCost s B ∧
      QueryExecution.PrefixBound QueryVisitorProgram.baselineHead steps a (896*B+baselineCost s B) := by
  have hW : (a.stacks 141).length ≤ s.bound := by
    rw [s.source_offset a hs]
    exact s.bounded 141
  obtain ⟨rp,rm,rs,raw,shifted,nl,hl,hcl,hbl,_,_,_⟩ :=
    QueryVisitorLoad.load_run_polynomial s.input s.source s.ready s.bound s.bounded s.rows
      s.addressRegisters s.dimensionRegisters s.cacheRegisters s.cacheWords s.cache
      a hs z B s.bound hz ha hW hcap
  let loaded:=QueryVisitorLoad.result s.input z a rp rm rs raw shifted
  have hfl : QueryMasterFrame a loaded := QueryVisitorLoad.result_query_master_frame ..
  have hhigh (i : Fin 896) (hi : 768 ≤ i.val) (hne : i∉([846,847] : List (Fin 896))) :
      loaded.stacks i=a.stacks i :=
    QueryVisitorLoad.result_high_frame s.input z a rp rm rs raw shifted i hi hne
  have hmask : loaded.stacks 670=mask s z := QueryVisitorLoad.result_mask_word ..
  have hcount : HighIncidenceProgram.Restriction.highCount (loaded.stacks 670)=
      (selectedHeads s.input.n s.input.rows s.input.low z).length :=
    QueryVisitorLoad.result_mask_count ..
  have hword' : (loaded.stacks 838).length=
      HighIncidenceProgram.Restriction.highCount (loaded.stacks 670) := by
    rw [hhigh 838 (by decide) (by decide),hcount]
    exact hword
  have hbase' : (loaded.stacks 670).length=(loaded.stacks 869).length := by
    rw [QueryVisitorLoad.result_mask_length,hhigh 869 (by decide) (by decide),hbase]
  obtain ⟨ni,ri,hi,hri,hmi,hvi,hfi,hbi,hbaseline,hregs,hci,_⟩ :=
    QueryVisitorProgram.install_run (hr.frame hfl)
      (hm.frame (hhigh 851 (by decide) (by decide)))
      (hv.frame (hhigh 852 (by decide) (by decide))) hbl
      ((hhigh 841 (by decide) (by decide)).trans htmp) hword' hbase'
  have he : Eval QueryVisitorProgram.baselineHead (nl+ni) a (installedRepresentative loaded ri) :=
    hl.seq hi
  have hc : nl+ni ≤ baselineCost s B := by unfold baselineCost; omega
  refine ⟨nl+ni,_,he,hri,hmi,hvi,hfl.trans hfi,hbi,?_,?_,?_,?_,hc,?_⟩
  · simpa only [hmask,hhigh 838 (by decide) (by decide),hhigh 869 (by decide) (by decide)] using hbaseline
  · rw [hbaseline,LeafAssignmentMergeProgram.merge_length,
      QueryRepresentativeFold.zeroMerge_length,QueryVisitorLoad.result_mask_length]
  · intro i hi' hnot
    have hload : i∉([846,847] : List (Fin 896)) := by
      intro hm
      rcases List.mem_cons.mp hm with hh | hh
      · exact hnot (List.mem_cons.mpr (Or.inl hh))
      · exact hnot (List.mem_cons.mpr (Or.inr
          (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hh)))))
    have hinstall : i∉([145,859,869,872,873,874,875,876,877] : List (Fin 896)) := by
      have h145 : i≠145 := by
        intro hh
        subst i
        change 768 ≤ (145 : ℕ) at hi'
        omega
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hnot ⊢
      exact ⟨h145,hnot.2.2⟩
    exact (installedRepresentative_frame loaded ri i hinstall).trans (hhigh i hi' hload)
  · intro i hi'
    exact (hregs i hi').trans (QueryVisitorLoad.result_register_frame s.input z a rp rm rs raw shifted i hi')
  · exact (QueryExecution.prefix_local QueryVisitorProgram.baselineHead _ B a ha).mono (by omega)


open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_head_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_head_oai
