-- Prove2me | solution 1 for O3.Stage2RouteB.coordinate_power_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:21:26.296732+00:00
-- url     : https://prove2.me/submissions/3a25d01f-738c-4d02-8a0e-7d81486ec440

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
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
open O3 O3.Stage2RouteB
namespace O3.Stage2RouteB
theorem _root_.solution {p a : ℝ} (hp : 1 < p) :
    |a| ^ (p - 2) * a * a = |a| ^ p := by
  by_cases ha : a = 0
  · subst a
    simp only [abs_zero]
    rw [show 0 ^ (p - 2) * 0 * 0 = (0 : ℝ) by ring]
    exact (Real.zero_rpow (by linarith : p ≠ 0)).symm
  · have habs : 0 < |a| := abs_pos.mpr ha
    calc
      |a| ^ (p - 2) * a * a = |a| ^ (p - 2) * |a| ^ (2 : ℕ) := by
        rw [sq_abs]
        ring
      _ = |a| ^ p := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_add habs]
        congr 1
        ring
end O3.Stage2RouteB
