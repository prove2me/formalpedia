-- Prove2me | solution 1 for O3.Stage2RouteB.squaredLpEnergy_eq_quadraticRegularizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:23.817963+00:00
-- url     : https://prove2.me/submissions/afac3a5b-62b5-48df-876f-62bce94cf34f

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_Stage2RouteB
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_nonneg
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
theorem _root_.solution {p : ℝ} (_hp : 0 < p)
    {d : ℕ} (x : Point d) :
    squaredLpEnergy p x = quadraticRegularizer p 0 x := by
  simp only [squaredLpEnergy, quadraticRegularizer, sub_zero, lpNorm]
  congr 1
  calc
    lpPower p x ^ (2 / p) = lpPower p x ^ ((1 / p) * 2) := by
      congr 1
      ring
    _ = (lpPower p x ^ (1 / p)) ^ (2 : ℝ) :=
      Real.rpow_mul (lpPower_nonneg p x) _ _
    _ = (lpPower p x ^ (1 / p)) ^ (2 : ℕ) := by rw [Real.rpow_two]
end O3.Stage2RouteB
