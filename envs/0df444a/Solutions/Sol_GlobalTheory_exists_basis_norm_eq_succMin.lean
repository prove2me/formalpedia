-- Prove2me | solution 1 for GlobalTheory.exists_basis_norm_eq_succMin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:05:16.684577+00:00
-- url     : https://prove2.me/submissions/7b06dde5-9834-49e8-90e5-85e9a7c4b7c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsLinearIndependentNormLeSuccMin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsLinearIndependentSqrtEqSuccMinQuad
import Theorems.Thm_GlobalTheory_exists_linearIndependent_norm_eq_succMin
import Theorems.Thm_GlobalTheory_finrank_span_of_isZLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Submodule
open GlobalTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L : Submodule ℤ E} {n : ℕ}
variable [FiniteDimensional ℝ E] [DiscreteTopology L]
variable (L) [IsZLattice ℝ L]
namespace GlobalTheory
theorem _root_.solution :
    ∃ b : Basis (Fin (finrank ℝ E)) ℝ E, (∀ j, b j ∈ L) ∧
      ∀ j : Fin (finrank ℝ E), ‖b j‖ = succMin L (j + 1) := by
  obtain ⟨v, hv, hL, hN⟩ :=
    exists_linearIndependent_norm_eq_succMin (L := L) (finrank_span_of_isZLattice L).ge
  have htop : ⊤ ≤ span ℝ (Set.range v) := by
    rw [top_le_iff]
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_eq_card hv, Fintype.card_fin]
  exact ⟨Basis.mk hv htop, by simpa using hL, by simpa using hN⟩
end GlobalTheory
