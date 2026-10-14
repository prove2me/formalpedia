-- Prove2me | solution 1 for L0BnB.Strength.psi1_eq_on_box
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-13T02:11:39.170082+00:00
-- url     : https://prove2.me/submissions/36ca73bb-f128-4b8c-918b-e562b4302aea

import Definitions.Def_L0BnB_Strength_Penalties
import Definitions.Def_L0BnB_Strength_Relaxations
import Mathlib


open L0BnB.Strength L0BnB.Reduced

theorem solution (lam0 lam2 M b : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2)
    (hregime : M < Real.sqrt (lam0 / lam2)) (hb : |b| ≤ M) :
    L0BnB.Reduced.psi1 lam0 lam2 b = 2 * |b| * Real.sqrt (lam0 * lam2) := by
  let r := Real.sqrt (lam2/lam0)
  have hr : 0 < r := Real.sqrt_pos_of_pos (div_pos hlam2 hlam0)
  have hr2 : lam0*r^2 = lam2 := by
    dsimp [r]
    rw [Real.sq_sqrt (div_nonneg hlam2.le hlam0.le)]
    field_simp
  have hsr : Real.sqrt (lam0/lam2)*r = 1 := by
    dsimp [r]
    rw [← Real.sqrt_mul (div_nonneg hlam0.le hlam2.le)]
    rw [show lam0/lam2*(lam2/lam0) = 1 by field_simp]
    norm_num
  have hs : |b*r| ≤ 1 := by
    rw [abs_mul, abs_of_pos hr]
    have h := mul_lt_mul_of_pos_right (hb.trans_lt hregime) hr
    linarith
  have heq : lam0*r = Real.sqrt (lam0*lam2) := by
    calc
      lam0*r = Real.sqrt ((lam0*r)^2) := (Real.sqrt_sq (mul_nonneg hlam0.le hr.le)).symm
      _ = Real.sqrt (lam0*lam2) := by
        congr 1
        nlinarith [congrArg (fun z : ℝ => lam0*z) hr2]
  change 2*lam0*reverseHuber (b*r) = _
  rw [reverseHuber, if_pos hs, abs_mul, abs_of_pos hr]
  calc
    _ = 2 * |b| * (lam0*r) := by ring
    _ = _ := by rw [heq]
