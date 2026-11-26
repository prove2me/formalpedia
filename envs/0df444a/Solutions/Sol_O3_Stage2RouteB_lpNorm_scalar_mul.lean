-- Prove2me | solution 1 for O3.Stage2RouteB.lpNorm_scalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:28.400708+00:00
-- url     : https://prove2.me/submissions/8659f2b7-d113-4ce3-a9e3-2f869e0df980

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_lpPower_scalar_mul
import Theorems.Thm_O3_lpPower_nonneg


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {r a : ℝ} (hr : 0 < r) {d : ℕ} (z : Point d) :
    lpNorm r (fun i ↦ a * z i) = |a| * lpNorm r z := by
  unfold lpNorm
  rw [lpPower_scalar_mul]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg a) r) (lpPower_nonneg r z)]
  rw [← Real.rpow_mul (abs_nonneg a)]
  rw [show r * (1 / r) = 1 by field_simp [ne_of_gt hr]]
  rw [Real.rpow_one]
end O3.Stage2RouteB
