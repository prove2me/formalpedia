-- Prove2me | solution 1 for O3.Stage2RouteB.abs_powerDuality_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:20:29.221795+00:00
-- url     : https://prove2.me/submissions/1b977089-e899-4ead-a64b-ed35917e856c

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
    |(|a| ^ (p - 2) * a)| = |a| ^ (p - 1) := by
  by_cases ha : a = 0
  · subst a
    simp only [abs_zero, mul_zero]
    rw [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · have habs : 0 < |a| := abs_pos.mpr ha
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg habs.le _)]
    calc
      |a| ^ (p - 2) * |a| = |a| ^ (p - 2) * |a| ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = |a| ^ ((p - 2) + 1) := (Real.rpow_add habs _ _).symm
      _ = |a| ^ (p - 1) := by
        congr 1
        ring
end O3.Stage2RouteB
