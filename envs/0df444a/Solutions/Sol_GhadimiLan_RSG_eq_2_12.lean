-- Prove2me | solution 1 for GhadimiLan.RSG.eq_2_12
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-08T22:26:04.305827+00:00
-- url     : https://prove2.me/submissions/3873609b-9285-4320-9d4b-b5ac4026be2a

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
import Definitions.Def_GhadimiLan_RSG_Model
import Theorems.Thm_ConvexOptAlg_SmoothGD_eq_3_6
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
open GhadimiLan.RSG
set_option autoImplicit false

/-- Eq. (2.12): co-coercivity (1.8) applied to the pair `(y, x*)` with `∇f(x*) = 0`. -/
theorem solution {n : ℕ} (f : E n → ℝ) (g : E n → E n) (L : ℝ)
    (hf : ConvexOptAlg.SmoothGD.IsBetaSmooth f g L) (hL : 0 < L)
    (hconv : ConvexOn ℝ Set.univ f) (xstar : E n) (hxstar : g xstar = 0) (y : E n) :
    1 / L * ‖g y‖ ^ 2 ≤ ⟪g y, y - xstar⟫_ℝ := by
  have h := ConvexOptAlg.SmoothGD.eq_3_6 f g L hL hconv hf y xstar
  simpa [hxstar] using h
