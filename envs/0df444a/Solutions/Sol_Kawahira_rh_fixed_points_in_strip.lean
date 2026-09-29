-- Prove2me | solution 1 for Kawahira.rh_fixed_points_in_strip
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:07:52.885574+00:00
-- url     : https://prove2.me/submissions/dc77aa55-c5d0-4bae-adf0-22a3d7234bb9

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nu_at_zero_of_order
import Theorems.Thm_Kawahira_norm_one_sub_inv
import Theorems.Thm_Kawahira_riemannZeta_analyticOrderAt_ne_top

open Complex Topology
open Kawahira

theorem solution
    (hRH : ∀ s : ℂ, IsNontrivialZero s → s.re = 1 / 2)
    (a : ℂ) (ha_re_pos : 0 < a.re) (ha_re_lt : a.re < 1)
    (hreg : riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0) (hfix : nuZeta a = a) :
    riemannZeta a = 0 ∧ a.re = 1 / 2 ∧
      (deriv riemannZeta a ≠ 0 → IsIndifferentFixedPoint nuZeta a) ∧
      (deriv riemannZeta a = 0 → IsAttractingFixedPoint nuZeta a) := by
  have ha0 : a ≠ 0 := by
    intro ha
    subst a
    norm_num at ha_re_pos
  have ha1 : a ≠ 1 := by
    intro ha
    subst a
    norm_num at ha_re_lt
  have hzeta : riemannZeta a = 0 := by
    rcases hreg with hz | hderiv
    · exact hz
    · by_contra hz
      have hquot : riemannZeta a / (a * deriv riemannZeta a) = 0 := by
        have heq : a - riemannZeta a / (a * deriv riemannZeta a) = a := by
          simpa [nuZeta, nu] using hfix
        exact sub_eq_self.mp heq
      exact (div_ne_zero hz (mul_ne_zero ha0 hderiv)) hquot
  have hnontrivial : IsNontrivialZero a := by
    refine ⟨hzeta, ?_⟩
    intro n hn
    have hre := congrArg Complex.re hn
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have hre : a.re = 1 / 2 := hRH a hnontrivial
  have han : AnalyticAt ℂ riemannZeta a :=
    analyticOn_riemannZeta a (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ha1)
  refine ⟨hzeta, hre, ?_, ?_⟩
  · intro hderiv
    have horder : analyticOrderAt riemannZeta a = (1 : ℕ∞) :=
      han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hzeta hderiv
    have hnu := Kawahira.nu_at_zero_of_order riemannZeta a 1 ha0 (by norm_num) han horder
    refine ⟨hfix, ?_⟩
    have hderiv_nu : deriv nuZeta a = 1 - a⁻¹ := by
      simpa [nuZeta] using hnu.2
    rw [hderiv_nu]
    exact (Kawahira.norm_one_sub_inv a ha0).1.2 hre
  · intro hderiv
    let m := analyticOrderNatAt riemannZeta a
    have hfinite := Kawahira.riemannZeta_analyticOrderAt_ne_top a ha1
    have horder : analyticOrderAt riemannZeta a = (m : ℕ∞) := by
      exact (Nat.cast_analyticOrderNatAt hfinite).symm
    have horder_ge : (2 : ℕ∞) ≤ analyticOrderAt riemannZeta a := by
      change (↑(2 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta a
      rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero han]
      intro i hi
      interval_cases i <;> simp [hzeta, hderiv]
    have hm : 2 ≤ m := by
      rw [horder] at horder_ge
      exact_mod_cast horder_ge
    have hnu := Kawahira.nu_at_zero_of_order riemannZeta a m ha0 (by omega) han horder
    refine ⟨hfix, ?_⟩
    have hderiv_nu : deriv nuZeta a = 1 - ((m : ℂ) * a)⁻¹ := by
      simpa [nuZeta, div_eq_mul_inv] using hnu.2
    rw [hderiv_nu]
    have hma : (m : ℂ) * a ≠ 0 := mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0)) ha0
    apply (Kawahira.norm_one_sub_inv ((m : ℂ) * a) hma).2.2
    have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
    have hm_re : ((m : ℂ).re) = (m : ℝ) := by norm_num
    have hm_im : ((m : ℂ).im) = 0 := by norm_num
    rw [mul_re, hm_re, hm_im, zero_mul, sub_zero, hre]
    nlinarith
