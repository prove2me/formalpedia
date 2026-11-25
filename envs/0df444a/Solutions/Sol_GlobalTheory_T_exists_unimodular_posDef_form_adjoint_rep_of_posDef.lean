-- Prove2me | solution 1 for GlobalTheory.T.exists_unimodular_posDef_form_adjoint_rep_of_posDef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:19:58.850908+00:00
-- url     : https://prove2.me/submissions/7576f80c-78b2-49d3-a759-abc4c772ea92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointActionStatement
import Theorems.Thm_GlobalTheory_exists_unimodular_posDef_adjoint_action


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ) (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ), 1 ≤ m → B0.transpose = B0 → (B0.map (Int.cast : ℤ → ℝ)).PosDef → (∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) → ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ), 1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧ ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by
  first | exact @GlobalTheory.exists_unimodular_posDef_adjoint_action | exact GlobalTheory.exists_unimodular_posDef_adjoint_action | (intros; apply GlobalTheory.exists_unimodular_posDef_adjoint_action <;> assumption)
end _root_.GlobalTheory.T
