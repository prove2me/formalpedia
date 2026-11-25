-- Prove2me | solution 1 for GlobalTheory.T.exists_log_near_one_unitaryGroup_of_form_linear_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:18:22.564313+00:00
-- url     : https://prove2.me/submissions/681ce18a-f548-458c-b908-6e1c58659a83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLogNearOneUnitaryGroupOfFormLinearBoundStatement
import Theorems.Thm_GlobalTheory_UnitaryLog_exists_log_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), IsUnit G.det → ∃ δ₁ C : ℝ, 0 < δ₁ ∧ ∀ (u : Matrix (Fin n) (Fin n) ℂ) (δ : ℝ), uᴴ * G * u = G → δ ≤ δ₁ → (∀ i j, ‖(u - 1) i j‖ ≤ δ) → ∃ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ * G + G * X = 0 ∧ NormedSpace.exp X = u ∧ ∀ i j, ‖X i j‖ ≤ C * δ := by
  first | exact @GlobalTheory.UnitaryLog.exists_log_unitary | exact GlobalTheory.UnitaryLog.exists_log_unitary | (intros; apply GlobalTheory.UnitaryLog.exists_log_unitary <;> assumption)
end _root_.GlobalTheory.T
