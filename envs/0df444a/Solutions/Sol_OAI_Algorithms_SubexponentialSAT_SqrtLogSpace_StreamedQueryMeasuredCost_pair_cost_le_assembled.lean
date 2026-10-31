-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:05:11.166423+00:00
-- url     : https://prove2.me/submissions/081f70a5-2190-4fec-9562-9016ba107417

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_TupleRunBudgets_run_bounds

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_AttainedSignatures
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFinite _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
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

theorem representative_exists (hN : 0 < N) : Nonempty (Representative key) :=
  ⟨⟨⟨0, hN⟩, by intro j hj; exact (Nat.not_lt_zero _ hj).elim⟩⟩

theorem card_representative_pos (hN : 0 < N) : 0 < Nat.card (Representative key) := by
  let _ := representative_exists key hN
  exact Nat.card_pos

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.AttainedSignatures
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_BooleanDifferences
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Boolean finite differences (ETH, Lemma `boolean-differences`).
The finite sets in this module specify sums; they are not operational enumerators. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences

open scoped BigOperators

theorem pairFamily_card_le (n J : ℕ) :
    (pairFamily n J).card ≤ (supportFamily n J).card ^ 2 := by
  calc
    _ ≤ (supportFamily n J ×ˢ supportFamily n J).card := Finset.card_filter_le _ _
    _ = _ := by simp [pow_two]

theorem pairFamily_eq_biUnion (n J : ℕ) :
    pairFamily n J = (supportFamily n J).biUnion
      (fun E => E.powerset.image (fun U => (E, U))) := by
  ext p
  rcases p with ⟨E, U⟩
  simp [Finset.mem_biUnion, Finset.mem_image]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.BooleanDifferences
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DifferencePairs
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Pruned finite-difference traversal. `none`, `some false`, and `some true`
encode membership in neither set, in `E \ U`, and in `U`, respectively.
`words` specifies visit order; the streaming fold does not construct it. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs

open scoped BigOperators
open BooleanDifferences

theorem pairCount_eq_sum (n J : ℕ) :
    pairCount n J = ∑ j ∈ Finset.range J, 2 ^ j * n.choose j := by
  have pascal (n J : ℕ) :
      (∑ j ∈ Finset.range (J + 1), 2 ^ j * (n + 1).choose j) =
        (∑ j ∈ Finset.range (J + 1), 2 ^ j * n.choose j) +
          2 * ∑ j ∈ Finset.range J, 2 ^ j * n.choose j := by
    induction J with
    | zero => simp
    | succ J ih =>
        rw [Finset.sum_range_succ _ (J + 1), ih,
          Nat.choose_succ_succ, Finset.sum_range_succ _ (J + 1),
          Finset.sum_range_succ _ J, pow_succ]
        ring
  induction n generalizing J with
  | zero =>
      cases J with
      | zero => simp
      | succ J => simp [pairCount, Finset.sum_range_succ']
  | succ n ih =>
      cases J with
      | zero => simp
      | succ J => rw [pairCount, ih, ih, pascal]

theorem pairFamily_card (n J : ℕ) : (pairFamily n J).card = pairCount n J := by
  rw [pairFamily_eq_biUnion]
  have disjoint : (↑(supportFamily n J) : Set (Finset (Fin n))).PairwiseDisjoint
      (fun E => E.powerset.image (fun U => (E, U))) := by
    intro E _ F _ hEF
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨U, _, hU⟩ := Finset.mem_image.mp hp
    obtain ⟨V, _, hV⟩ := Finset.mem_image.mp hq
    exact hEF (congrArg Prod.fst (hU.trans hV.symm))
  rw [Finset.card_biUnion disjoint]
  simp_rw [Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2),
    Finset.card_powerset]
  have hdisjoint : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint
      (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) := by
    intro i _ j _ hij
    exact Finset.pairwise_disjoint_powersetCard _ hij
  have hs : supportFamily n J = (Finset.range J).disjiUnion
      (fun j => (Finset.univ : Finset (Fin n)).powersetCard j) hdisjoint := by
    ext E
    rw [mem_supportFamily, Finset.mem_disjiUnion]
    constructor
    · intro hE
      exact ⟨E.card, Finset.mem_range.mpr hE,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ E, rfl⟩⟩
    · rintro ⟨j, hj, hE⟩
      exact (Finset.mem_powersetCard.mp hE).2 ▸ Finset.mem_range.mp hj
  rw [hs, Finset.sum_disjiUnion, pairCount_eq_sum]
  apply Finset.sum_congr rfl
  intro j _
  have h := Finset.sum_powersetCard j (Finset.univ : Finset (Fin n)) (fun a => 2 ^ a)
  rw [nsmul_eq_mul] at h
  simpa [Nat.mul_comm] using h

theorem pairCount_le_square (n J : ℕ) : pairCount n J ≤ (supportFamily n J).card ^ 2 := by
  rw [← pairFamily_card]
  exact pairFamily_card_le n J

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DifferencePairs
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SquarefreeSupportCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.Squarefree.Sparse

open scoped BigOperators

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem supportUniverse_eq_disjiUnion (vars : Finset V) (J : ℕ) :
    supportUniverse vars J = (Finset.range J).disjiUnion
      (fun j => vars.powersetCard j)
      (powersetCard_pairwiseDisjoint vars J) := by
  ext s
  rw [Finset.mem_disjiUnion]
  simp only [supportUniverse, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨hs, hc⟩
    exact ⟨s.card, hc, hs, rfl⟩
  · rintro ⟨j, hj, hs, hc⟩
    exact ⟨hs, hc.trans_lt hj⟩

omit [DecidableEq V] in
theorem supportUniverse_card (vars : Finset V) (J : ℕ) :
    (supportUniverse vars J).card = ∑ j ∈ Finset.range J, vars.card.choose j := by
  rw [supportUniverse_eq_disjiUnion, Finset.card_disjiUnion]
  simp

theorem finite_support_count (n J : ℕ) :
    (supportUniverse (Finset.univ : Finset (Fin n)) J).card =
      ∑ j ∈ Finset.range J, n.choose j := by
  simp [supportUniverse_card]

end SubexponentialSAT.SqrtLog.Squarefree.Sparse

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_SupportProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.StackCompiler.stateFintype _root_.OAI.Algorithms.SubexponentialSAT.StructuredProgram.siteFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.SupportProgram

open scoped BigOperators

theorem count_eq_supportUniverse (n J : ℕ) :
    count n J = (Squarefree.Sparse.supportUniverse (Finset.univ : Finset (Fin n)) J).card :=
  (Squarefree.Sparse.finite_support_count n J).symm

end SubexponentialSAT.SqrtLog.SupportProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SupportCountBridge
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The active-coordinate pair iterator is paid by the supplied ambient
support envelope. These are cardinality comparisons, not stored families. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

open BooleanDifferences

theorem supportFamily_card_eq_count (n J : ℕ) :
    (supportFamily n J).card = SqrtLog.SupportProgram.count n J := by
  rw [SqrtLog.SupportProgram.count_eq_supportUniverse]
  congr 1

theorem pairCount_le_ambient_support_square {m n : ℕ} (hmn : m ≤ n) (J : ℕ) :
    DifferencePairs.pairCount m J ≤ SqrtLog.SupportProgram.count n J ^ 2 := by
  have hcount : SqrtLog.SupportProgram.count m J ≤
      SqrtLog.SupportProgram.count n J := by
    unfold SqrtLog.SupportProgram.count
    exact Finset.sum_le_sum (fun j _ => Nat.choose_le_choose j hmn)
  calc
    DifferencePairs.pairCount m J ≤ (supportFamily m J).card ^ 2 :=
      DifferencePairs.pairCount_le_square m J
    _ = SqrtLog.SupportProgram.count m J ^ 2 := by rw [supportFamily_card_eq_count]
    _ ≤ SqrtLog.SupportProgram.count n J ^ 2 := Nat.pow_le_pow_left hcount 2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamedQueryCostBudgets
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The new traversal charges only attained full integer signatures. Its
predecessor rescans and complete-tuple visitors are additive, and the pair
count is bounded by the square of the original ambient support count. These
numerical comparisons use fixed powers of the original explicit cost; they
do not assert a machine execution or supply an evaluator service. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets

open scoped BigOperators
open OAI.Algorithms.SubexponentialSAT.SqrtLog SignatureTupleDFS SignatureTupleTraversal
open MulticolorTypes Subexp.ConstructivePacking LayoutExactBuckets

noncomputable section
open Classical

/-- These are the actual first-occurrence counts. In particular a traversal
with no heads still has its one empty complete tuple. -/
theorem attained_inventory_pos {h : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (i : ℕ) → Fin (2 ^ h i) → κ i) (levels : ℕ) :
    1 ≤ prefixCount (fun i => Fintype.card (Representatives key i)) levels := by
  apply Finset.one_le_prod'
  intro i _
  have hpositive : 0 < Fintype.card (Representatives key i) := by
    simpa only [Nat.card_eq_fintype_card] using
      AttainedSignatures.card_representative_pos (key i) (pow_pos (by omega) _)
  omega

/-- The support and signature factors occur together in the original
explicit budget. Positive actual call, branch and bit counters pay them. -/
theorem support_enumeration_le_sparseWork
    (n J setup calls branches base rows heads headSize bits ordinary : ℕ)
    (hcalls : 1 ≤ calls) (hbranches : 1 ≤ branches) (hbits : 1 ≤ bits) :
    SupportProgram.count n J * CostAssembly.enumerationWork base rows heads headSize ≤
      CostAssembly.sparseWork n J setup calls branches
        (CostAssembly.enumerationWork base rows heads headSize) bits ordinary := by
  have ho : 1 ≤ (ordinary + 1) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have hs : SupportProgram.count n J ≤ (SupportProgram.count n J + 1) ^ 4 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  unfold CostAssembly.sparseWork
  calc
    _ = 1 * 1 * CostAssembly.enumerationWork base rows heads headSize * 1 * 1 *
        SupportProgram.count n J := by ring
    _ ≤ calls * branches * CostAssembly.enumerationWork base rows heads headSize *
        bits * (ordinary + 1) ^ 8 * (SupportProgram.count n J + 1) ^ 4 := by gcongr
    _ ≤ _ := Nat.le_add_left _ _

theorem inventory_head_le_enumeration (K H base rows heads headSize : ℕ)
    (hK : K ≤ base ^ rows) (hH : H ≤ headSize) (hheads : 1 ≤ heads) :
    K * 2 ^ H ≤ CostAssembly.enumerationWork base rows heads headSize := by
  unfold CostAssembly.enumerationWork
  calc
    _ ≤ base ^ rows * 2 ^ headSize := Nat.mul_le_mul hK
      (Nat.pow_le_pow_right (by decide) hH)
    _ = base ^ rows * 1 * 2 ^ headSize := by ring
    _ ≤ _ := by gcongr

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryCostBudgets
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_TruncatedRingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Native arithmetic after immediate Boolean specialization

The existing finite sparse-product program is used with empty formal support.
Its keys still carry the ambient input coordinate type; this does not compress
the declared variables. There are at most `u * J` retained entries, including
zero cutoffs. Polynomial local time therefore bounds all its source prefixes,
including the table, inputs, output, normalization copies and arithmetic scratch.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram

open scoped BigOperators
open OAI OAI.Algorithms.SubexponentialSAT.SqrtLog OAI.Algorithms.SubexponentialSAT.SubexpLiftRing OAI.Algorithms.SubexponentialSAT.SubexpQuarticRing
open MomentsProgram BitProgram

/- The two fields coincide with LeafProgram.NativeSemantics.Good. The
arithmetic layer states them transparently to avoid importing the factor
interpreter. Conversion in either direction supplies `valid` and `nodup`.
The proof bodies below are the original finite-program validity arguments. -/

variable {V R : Type*} [DecidableEq V] [CommRing R]

private theorem localBudget_mono (n B d u J N a : ℕ)
    (hn : n ≤ a) (hB : B ≤ a) (hd : d ≤ a) (hu : u ≤ a) (hJ : J ≤ a) (hN : N ≤ a) :
    localBudget n B d u J N ≤ localBudget a a a a a a := by
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  gcongr

/-- The degree and constant are fixed before every runtime dimension. -/
theorem localBudget_le (n B d u J N : ℕ) :
    localBudget n B d u J N ≤ 3000000 * (n + B + d + u + J + N + 1) ^ 10 := by
  let a := n + B + d + u + J + N + 1
  have ha : 1 ≤ a := by dsimp [a]; omega
  refine (localBudget_mono n B d u J N a (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega) (by dsimp [a]; omega) (by dsimp [a]; omega)
    (by dsimp [a]; omega)).trans ?_
  change localBudget a a a a a a ≤ 3000000 * a ^ 10
  have h0 : 1 ≤ a ^ 10 := Nat.one_le_pow 10 a ha
  have h1 : a ≤ a ^ 10 := by simpa using pow_le_pow_right' ha (show 1 ≤ 10 by decide)
  have h2 : a ^ 2 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h3 : a ^ 3 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h4 : a ^ 4 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h5 : a ^ 5 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h6 : a ^ 6 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h7 : a ^ 7 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h8 : a ^ 8 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  have h9 : a ^ 9 ≤ a ^ 10 := pow_le_pow_right' ha (by decide)
  dsimp [localBudget, normalizationBudget, additionBudget, scalingBudget, productBudget,
    Product.stepEnvelope, MomentsReadoutProgram.uniformReadoutBudget,
    MomentsReadoutProgram.uniformSlotBudget, Dictionary.codeBranchBudget]
  ring_nf
  omega

theorem additionBudget_le_local (n B d u J N : ℕ) :
    additionBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

theorem scalingBudget_le_local (n B d u J N : ℕ) :
    scalingBudget n B d u J ≤ localBudget n B d u J N := by
  unfold localBudget
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.TruncatedRingProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_NodeTimeColumns
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage
open LeafHeadSetupProgram LeafHeadSetupProgram.Bounds
open LayoutProgram RowSelectionProgram

theorem inputBounds (s : Native.Inputs) (a : LeafHeadSetupProgram.Data)
    (h : Native.Ready s a) (B : ℕ) (hb : WordBound B a) : InputBounds s B := by
  have hp : (LayoutOwnerFiberProgram.stream s.plans).length ≤ B := by simpa only [h.plans] using hb 136
  have hc := Encoding.length_encodeList_lower (fun p : ℕ×ℕ => LayoutOwnerFiberProgram.pairPayload p.1 p.2) s.plans
  have hd : s.D ≤ B := by
    change s.plans.length+1 ≤ (LayoutOwnerFiberProgram.stream s.plans).length at hc
    rw [s.plans_length] at hc
    omega
  exact ⟨by simpa [h.ambient,unary] using hb 128,hd,
    by simpa [h.colors,unary] using hb 130,by simpa [h.nodes,unary] using hb 131,
    by simpa [h.order,unary] using hb 138,by simpa only [h.width] using hb 140,
    by simpa only [h.height] using hb 139,by simpa only [h.metadata] using hb 135,hp,
    by simpa [h.wordWidth,unary] using hb 132⟩

end SubexponentialSAT.SqrtLog.NodeTime

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamedQueryMeasuredCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The measured callback pays native mask setup, the complete attained-tuple
run (including ascent), and the signed commit. Its finite-difference iterator
is compared to the original explicit resource record with one fixed power. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost

open OAI SqrtLog SubexpLiftRing SubexpQuarticRing
open SignatureTupleSource SignatureTupleTraversal SignatureTupleDFS
open CostAssembly.Polynomial
open scoped BigOperators

theorem commit_le {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (N A : ℕ)
    (hn : n ≤ A) (hN : N ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A) (hJ : q.J ≤ A) :
    QueryPairEvaluation.commitBudget q N (QueryHeadBudgets.compact A) ≤ commitEnvelope A := by
  have hlocal := TruncatedRingProgram.localBudget_le n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hscale := TruncatedRingProgram.scalingBudget_le_local n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hadd := TruncatedRingProgram.additionBudget_le_local n (baseWidth 3 q.p.t) d q.p.t q.J 0
  have hb : TruncatedRingProgram.localBudget n (baseWidth 3 q.p.t) d q.p.t q.J 0 ≤
      3000000*(6*A+1)^10 := by
    apply hlocal.trans
    simp only [RingProgram.ternary_baseWidth]
    gcongr
    omega
  have hbytes : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤
      A*A*(2*(A+A+A)+2*(A*(2*A))+2) := by
    simp only [RingProgram.ternary_baseWidth]
    gcongr
  unfold QueryPairEvaluation.commitBudget QueryProgram.pairUpdateBudget
    QueryProgram.signedAccumulateBudget QueryProgram.signedScalingBudget commitEnvelope
  omega

/-- All callback coefficients are instantiated at the same compact cap as
the actual tuple run. No successful callback or evaluator is a hypothesis. -/
theorem callback_le (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (N A height : ℕ)
    (hN : N ≤ s.input.n) (hs : s.bound ≤ A) (hd : d ≤ A) (ht : q.p.t ≤ A)
    (hu : q.u ≤ A) (hJ : q.J ≤ A) (hR : q.p.R = s.input.R)
    (hw : q.p.width = s.input.width) (hp : q.p.power = s.input.power) :
    QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height ≤
      coefficient A*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by
  have hn := (NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded).n.trans hs
  have hstart : QueryPairEvaluation.startBudget s.input.n (QueryHeadBudgets.compact A) ≤
      QueryPairEvaluation.startBudget A (QueryHeadBudgets.compact A) := by
    unfold QueryPairEvaluation.startBudget
    omega
  have hcommit := commit_le q N A hn (hN.trans hn) hd ht hJ
  have hrun := (TupleRunBudgets.run_bounds s q A hs hd ht hu hJ hR hw hp).2 height
  have hK : 1 ≤ SignatureTupleRun.tupleCount s.key s.input.r :=
    StreamedQueryCostBudgets.attained_inventory_pos s.key s.input.r
  have hfactor : 1 ≤ (s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by
    simpa only [one_mul] using Nat.mul_le_mul
      (Nat.mul_le_mul (show 1 ≤ s.input.r+1 by omega) hK)
      (Nat.one_le_pow height 4 (by decide))
  have hpaid : QueryPairEvaluation.startBudget s.input.n (QueryHeadBudgets.compact A)+
      QueryPairEvaluation.commitBudget q N (QueryHeadBudgets.compact A) ≤
      localEnvelope A*((s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height) := by
    apply (Nat.add_le_add hstart hcommit).trans
    exact (Nat.mul_one (localEnvelope A)).symm.le.trans (Nat.mul_le_mul_left _ hfactor)
  unfold QueryPairEvaluation.callbackBudget coefficient
  calc
    _ ≤ localEnvelope A*((s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height)+
        TupleRunBudgets.runCoefficient A*(s.input.r+1)*SignatureTupleRun.tupleCount s.key s.input.r*4^height := by omega
    _ = _ := by ring

private theorem square_inventory (M K H : ℕ) (hK : 1 ≤ K) :
    M^2*K*4^H ≤ (M*K*2^H)^2 := by
  have hk : K ≤ K^2 := by nlinarith
  calc
    _ ≤ M^2*K^2*4^H := by gcongr
    _ = _ := by rw [show (4:ℕ)=2^2 by norm_num,←pow_mul,mul_pow,mul_pow]; ring

/-- Actual start/run/commit and iterator costs are dominated by the square
of the original assembled budget. The remaining premises identify the actual
jet order, selected-rank inventory and balanced head maximum in that record. -/
theorem pair_cost_le_assembled_oai (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (k N n A height : ℕ) (p : CostAssembly.Resources)
    (hN : N ≤ s.input.n) (hsn : s.input.n ≤ n) (hs : s.bound ≤ A)
    (hd : d ≤ A) (ht : q.p.t ≤ A) (hu : q.u ≤ A) (hJ : q.J ≤ A)
    (hR : q.p.R = s.input.R) (hw : q.p.width = s.input.width) (hp : q.p.power = s.input.power)
    (horder : q.J = CostAssembly.jetOrder k n p)
    (hbits : 1 ≤ p.bits) (hheads : 1 ≤ p.heads)
    (hK : SignatureTupleRun.tupleCount s.key s.input.r ≤ p.labelBase^p.labelRows)
    (hheight : height ≤ p.headSize) :
    DifferencePairsProgram.cost
      (QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
        (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
        (QueryHeadBudgets.transient A) height) N q.J ≤
      pairCoefficient A*CostAssembly.assembledWork k n p^2+10 := by
  let K := SignatureTupleRun.tupleCount s.key s.input.r
  let M := SupportProgram.count n q.J
  have hk : 1 ≤ K := StreamedQueryCostBudgets.attained_inventory_pos s.key s.input.r
  have hi := NodeTime.inputBounds s.input s.source s.ready s.bound s.bounded
  have hna := hN.trans (hi.n.trans hs)
  have hra := hi.r.trans hs
  have hcb := callback_le s q N A height hN hs hd ht hu hJ hR hw hp
  have hfactor : 1 ≤ (s.input.r+1)*K*4^height := by
    simpa only [one_mul] using Nat.mul_le_mul
      (Nat.mul_le_mul (show 1 ≤ s.input.r+1 by omega) hk)
      (Nat.one_le_pow height 4 (by decide))
  have h46 : 46 ≤ 46*((s.input.r+1)*K*4^height) :=
    (Nat.mul_one 46).symm.le.trans (Nat.mul_le_mul_left _ hfactor)
  have hcallback : QueryPairEvaluation.callbackBudget s q N (QueryHeadBudgets.compact A)
      (QueryHeadBudgets.source A) (QueryHeadBudgets.arithmetic A)
      (QueryHeadBudgets.transient A) height+46 ≤ (coefficient A+46)*(s.input.r+1)*K*4^height := by
    calc
      _ ≤ coefficient A*(s.input.r+1)*K*4^height+46*((s.input.r+1)*K*4^height) := Nat.add_le_add hcb h46
      _ = _ := by ring
  have hcombined : M*K*2^height ≤ CostAssembly.assembledWork k n p := by
    dsimp only [M]
    rw [horder]
    rw [Nat.mul_assoc]
    apply (Nat.mul_le_mul_left _ (StreamedQueryCostBudgets.inventory_head_le_enumeration K height
      p.labelBase p.labelRows p.heads p.headSize hK hheight hheads)).trans
    exact StreamedQueryCostBudgets.support_enumeration_le_sparseWork n _ p.setup
      (CostAssembly.hashCalls n p.clauses (SparseCode.distanceDenom p.clauses p.initialOccurrence))
      (2^p.branchVars) p.labelBase p.labelRows p.heads p.headSize p.bits p.ordinary
      (by unfold CostAssembly.hashCalls; omega) (Nat.one_le_pow _ _ (by decide)) hbits
  have hpair : DifferencePairs.pairCount N q.J ≤ M^2 := pairCount_le_ambient_support_square (hN.trans hsn) q.J
  unfold DifferencePairsProgram.cost
  calc
    _ ≤ ((coefficient A+46)*(s.input.r+1)*K*4^height)*(3*N+1)*M^2+10 := by gcongr
    _ = (coefficient A+46)*(s.input.r+1)*(3*N+1)*(M^2*K*4^height)+10 := by ring
    _ ≤ pairCoefficient A*(M*K*2^height)^2+10 := by
      unfold pairCoefficient
      gcongr
      exact square_inventory M K height hk
    _ ≤ _ := by gcongr

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamedQueryMeasuredCost.pair_cost_le_assembled_oai
