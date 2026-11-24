-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:40:49.956199+00:00
-- url     : https://prove2.me/submissions/23c779c8-efc2-4441-9d6e-ca6db2dbddca

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JoinCol
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PAreaMultiplicityWeight
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SigmaCompactDisjointRefinement
import Theorems.Thm_GlobalTheory_CompanionTheory_CroftonPartition_isSigmaCompact_of_isOpen_compact
import Theorems.Thm_GlobalTheory_CompanionTheory_CroftonPartition_isSigmaCompact_inter_isClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CroftonPartition
namespace GlobalTheory.CompanionTheory.CroftonPartition
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) →
    (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X),
      Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧
      ∀ t, IsSigmaCompact (A t) := by
  intro X _ _ _ _ ι S hS hcov
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover S hS hcov.ge
  let e := t.equivFin
  let l : Fin t.card → ι := fun j => (e.symm j : ι)
  let A : Fin t.card → Set X := fun j => S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i)
  refine ⟨t.card, l, A, ?_, ?_, ?_, ?_⟩
  · intro j j' hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact Set.disjoint_left.2 fun x hx hx' => hx'.2 (Set.mem_iUnion₂.2 ⟨j, h, hx.1⟩)
    · exact Set.disjoint_left.2 fun x hx hx' => hx.2 (Set.mem_iUnion₂.2 ⟨j', h, hx'.1⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    have hl : l (e ⟨i, hit⟩) = i := by simp [l]
    obtain ⟨j, hj, hmin⟩ := wellFounded_lt.has_min {j : Fin t.card | x ∈ S (l j)}
      ⟨e ⟨i, hit⟩, by simpa [hl] using hxi⟩
    refine Set.mem_iUnion.2 ⟨j, hj, fun hx => ?_⟩
    obtain ⟨i', hi', hxi'⟩ := Set.mem_iUnion₂.1 hx
    exact hmin i' hxi' hi'
  · intro j
    exact Set.sdiff_subset
  · intro j
    show IsSigmaCompact (S (l j) \ ⋃ (i : Fin t.card) (_ : i < j), S (l i))
    rw [Set.sdiff_eq]
    exact isSigmaCompact_inter_isClosed (isSigmaCompact_of_isOpen_compact (hS _))
      (isClosed_compl_iff.2 (isOpen_iUnion fun i => isOpen_iUnion fun _ => hS _))
end GlobalTheory.CompanionTheory.CroftonPartition
