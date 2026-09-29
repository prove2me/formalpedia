-- Prove2me | solution 1 for Kawahira.nu_indifferent_zero_order_re
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:29:41.0733+00:00
-- url     : https://prove2.me/submissions/cccbe548-0027-4fd5-8bf0-af0a095d5345

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nu_at_zero_of_order
import Theorems.Thm_Kawahira_norm_one_sub_inv

open Complex Topology
open Kawahira

theorem solution (g : ℂ → ℂ) (a : ℂ) (m : ℕ)
    (ha : a ≠ 0) (hm : 1 ≤ m) (hg : AnalyticAt ℂ g a)
    (horder : analyticOrderAt g a = (m : ℕ∞))
    (hind : IsIndifferentFixedPoint (nu g) a) :
    (m : ℝ) * a.re = 1 / 2 := by
  have hnu := Kawahira.nu_at_zero_of_order g a m ha hm hg horder
  have hma : (m : ℂ) * a ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (show m ≠ 0 by omega)) ha
  have hnorm : ‖1 - ((m : ℂ) * a)⁻¹‖ = 1 := by
    have hderiv : deriv (nu g) a = 1 - ((m : ℂ) * a)⁻¹ := by
      simpa [div_eq_mul_inv] using hnu.2
    rw [← hderiv]
    exact hind.2
  have hre := (Kawahira.norm_one_sub_inv ((m : ℂ) * a) hma).1.1 hnorm
  have hm_re : ((m : ℂ).re) = (m : ℝ) := by norm_num
  have hm_im : ((m : ℂ).im) = 0 := by norm_num
  simpa only [mul_re, hm_re, hm_im, zero_mul, sub_zero] using hre
