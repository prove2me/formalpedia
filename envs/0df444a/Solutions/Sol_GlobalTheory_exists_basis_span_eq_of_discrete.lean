-- Prove2me | solution 1 for GlobalTheory.exists_basis_span_eq_of_discrete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:05:21.2933+00:00
-- url     : https://prove2.me/submissions/987b4c3a-230f-4959-b9d5-4d3f12d277e4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsBasisSpanEqOfDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {N : ℕ} (M : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology M] (hM : span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤) :
    ∃ b : Basis (Fin N) ℝ (EuclideanSpace ℝ (Fin N)), span ℤ (Set.range b) = M := by
  have : IsZLattice ℝ M := ⟨hM⟩
  have := ZLattice.module_free ℝ M
  have := ZLattice.module_finite ℝ M
  let b1 := (Module.Free.chooseBasis ℤ M).ofZLatticeBasis ℝ M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = N := by
    rw [← finrank_eq_card_basis b1]
    simp
  refine ⟨b1.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Basis.range_reindex]
  exact Basis.ofZLatticeBasis_span ℝ M _
end GlobalTheory
