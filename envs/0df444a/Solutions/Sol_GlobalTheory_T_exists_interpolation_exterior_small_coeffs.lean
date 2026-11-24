-- Prove2me | solution 1 for GlobalTheory.T.exists_interpolation_exterior_small_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:09.382301+00:00
-- url     : https://prove2.me/submissions/70b40ca9-35f9-4f09-bf66-f8a220df5e0d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffs
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsInterpolationExteriorSmallCoeffsStatement
import Theorems.Thm_GlobalTheory_ExteriorInterpolation_interpolation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (l : ℕ) (z : Fin l → ℂ) (g : ℂ → ℂ) (r G : ℝ), 0 < r → r ≤ 1 → (∀ i, r < ‖z i‖ ∧ ‖z i‖ ≤ 1) → DifferentiableOn ℂ g {w | r ≤ ‖w‖} → Tendsto g (Filter.cocompact ℂ) (𝓝 0) → (∀ w : ℂ, ‖w‖ = r → ‖g w‖ ≤ G * ‖∏ i, (w - z i)‖) → ∃ c : Fin l → ℂ, (∀ i, ∑ j, c j * z i ^ (j : ℕ) = g (z i)) ∧ ∑ j, ‖c j‖ ≤ 4 ^ l * r * G := by
  first | exact @GlobalTheory.ExteriorInterpolation.interpolation | exact GlobalTheory.ExteriorInterpolation.interpolation | (intros; apply GlobalTheory.ExteriorInterpolation.interpolation <;> assumption)
end _root_.GlobalTheory.T
