-- Prove2me | solution 1 for O3.Stage2RouteC.lpNorm_fin_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:05:59.67873+00:00
-- url     : https://prove2.me/submissions/23fc24f9-9611-42fa-ba9f-0f80f7b19563

import Definitions.Def_O3_Geometry
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Normed.Lp.PiLp
import Definitions.Def_O3_Stage2RouteC
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteC
namespace O3.Stage2RouteC
theorem _root_.solution {p : ℝ} (hp : 0 < p) (x : O3.Point 1) :
    O3.lpNorm p x = |x 0| := by
  simp only [O3.lpNorm, O3.lpPower, Fin.sum_univ_one]
  rw [← Real.rpow_mul (abs_nonneg (x 0))]
  have hp0 : p ≠ 0 := hp.ne'
  rw [mul_one_div_cancel hp0, Real.rpow_one]
end O3.Stage2RouteC
