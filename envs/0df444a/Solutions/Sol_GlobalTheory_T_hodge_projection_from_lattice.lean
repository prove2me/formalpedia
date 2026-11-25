-- Prove2me | solution 1 for GlobalTheory.T.hodge_projection_from_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:26:36.065443+00:00
-- url     : https://prove2.me/submissions/8684fff4-31c5-498a-91db-9be373c93313

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionFromLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HodgeProjectionFromLatticeStatement
import Theorems.Thm_GlobalTheory_spanning_map_factors_through_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (W : Type 1) [AddCommGroup W] [Module ℂ W] (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (P : Λ →+ W)
    (F : Submodule ℂ W), Submodule.span ℂ (Set.range P) = ⊤ → Module.finrank ℂ W = 2 * g →
    Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ →
    (∀ c : Λ →₀ ℂ, (c.sum fun x r ↦ r • P x) ∈ F ↔ (c.sum fun x r ↦ r • (x : Fin g → ℂ)) = 0) →
    ∃ Q : W →ₗ[ℂ] (Fin g → ℂ), LinearMap.ker Q = F ∧ (∀ x, Q (P x) = x) ∧ Module.finrank ℂ F = g := by
  first | exact @GlobalTheory.spanning_map_factors_through_quotient | exact GlobalTheory.spanning_map_factors_through_quotient | (intros; apply GlobalTheory.spanning_map_factors_through_quotient <;> assumption)
end _root_.GlobalTheory.T
