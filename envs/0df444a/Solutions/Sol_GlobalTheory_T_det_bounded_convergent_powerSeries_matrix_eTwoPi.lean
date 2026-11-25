-- Prove2me | solution 1 for GlobalTheory.T.det_bounded_convergent_powerSeries_matrix_eTwoPi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:17:29.078213+00:00
-- url     : https://prove2.me/submissions/ee362910-1a0e-442c-90b3-b33f639a7ae6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DetBoundedConvergentPowerSeriesMatrixETwoPi
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DetBoundedConvergentPowerSeriesMatrixETwoPiStatement
import Theorems.Thm_GlobalTheory_det_bounded_eTwoPi


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (g : ℕ) (A : Matrix (Fin g) (Fin g) (PowerSeries ℂ)) (w₀ : ℂ), IsUnit A.det → (∀ i j, Summable (fun m : ℕ => PowerSeries.coeff m (A i j) * eTwoPi w₀ ^ m)) → ∃ T' C : ℝ, 0 < C ∧ ∀ w : ℂ, T' < w.im → C⁻¹ ≤ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ∧ ‖(Matrix.of fun i j => ∑' m : ℕ, PowerSeries.coeff m (A i j) * eTwoPi w ^ m).det‖ ≤ C := by
  first | exact @GlobalTheory.det_bounded_eTwoPi | exact GlobalTheory.det_bounded_eTwoPi | (intros; apply GlobalTheory.det_bounded_eTwoPi <;> assumption)
end _root_.GlobalTheory.T
