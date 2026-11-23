-- Prove2me | solution 3 for GrothendieckConstant.six_pi_div_eleven_le_grothendieckConst
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T15:45:38.958784+00:00
-- url     : https://prove2.me/submissions/a3fa0f59-b55d-405e-a7a1-baff12f5c727
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_GrothendieckConstant_affine_constraint_transfer
import Theorems.Thm_GrothendieckConstant_coeff_hermite_moments
import Theorems.Thm_GrothendieckLB_eq_35_36

open GrothendieckConstant GrothendieckLB

theorem solution : 6 * Real.pi / 11 ≤ grothendieckConst := by
  have htransfer := affine_constraint_transfer 1 (by norm_num) (by
    intro d S
    obtain ⟨hlinear, hcubic⟩ := coeff_hermite_moments d S
    change coeffLinear S = Real.pi / 2 * p1Inner S.f S.g at hlinear
    change coeffCubic S = Real.pi / 12 *
      ∑ i, ∑ j, ∑ l, cubicMoment S.f i j l * cubicMoment S.g i j l at hcubic
    have hcubic' : coeffCubic S = Real.pi / 2 * p3Inner S.f S.g := by
      rw [hcubic, p3Inner]
      ring
    have henergy := (eq_35_36 (f := S.f) (g := S.g)
      ⟨S.measurable_f, S.f_sign⟩ ⟨S.measurable_g, S.g_sign⟩).2.2
    have hscaled := mul_le_mul_of_nonneg_left henergy (by positivity : 0 ≤ Real.pi / 2)
    have hnorm : Real.pi / 2 * (11 / 6 * ABPOnline.cG ^ 2) = 11 / 6 := by
      rw [ABPOnline.cG, Real.sq_sqrt (by positivity : 0 ≤ 2 / Real.pi)]
      field_simp [Real.pi_ne_zero] <;> ring
    rw [hnorm] at hscaled
    rw [hlinear, hcubic']
    linarith only [hscaled])
  convert htransfer using 1 <;> ring
