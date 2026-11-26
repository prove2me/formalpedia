-- Prove2me | solution 1 for O3.Stage2RouteB.squaredLpEnergy_scalar_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:37.55617+00:00
-- url     : https://prove2.me/submissions/b2dc7e24-a78c-4133-926b-92c760676186

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_Stage2RouteB_lpPower_scalar_mul
import Theorems.Thm_O3_lpPower_nonneg


set_option autoImplicit true
open scoped BigOperators
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p a : ℝ} (hp : 0 < p) {d : ℕ} (h : Point d) :
    squaredLpEnergy p (fun i ↦ a * h i) = a ^ (2 : ℕ) * squaredLpEnergy p h := by
  rw [squaredLpEnergy, lpPower_scalar_mul, Real.mul_rpow
    (Real.rpow_nonneg (abs_nonneg a) p) (lpPower_nonneg p h)]
  have habsp : (|a| ^ p) ^ (2 / p) = |a| ^ (2 : ℝ) := by
    rw [← Real.rpow_mul (abs_nonneg a)]
    congr 1
    field_simp
  rw [habsp, Real.rpow_two]
  rw [sq_abs]
  unfold squaredLpEnergy
  ring
end O3.Stage2RouteB
