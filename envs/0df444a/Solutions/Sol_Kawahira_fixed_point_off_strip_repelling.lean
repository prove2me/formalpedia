-- Prove2me | solution 1 for Kawahira.fixed_point_off_strip_repelling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T22:43:31.992444+00:00
-- url     : https://prove2.me/submissions/ed55dfee-5a0c-4ce8-b0a3-7633c54ec0e5

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_nontrivial_zero_mem_strip
import Theorems.Thm_Kawahira_norm_one_sub_inv
import Theorems.Thm_Kawahira_nu_at_zero_of_order
import Theorems.Thm_riemannZeta_trivial_zero_order_one

open Complex Topology
open Kawahira

theorem solution (a : ℂ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hreg : riemannZeta a = 0 ∨ deriv riemannZeta a ≠ 0)
    (hout : ¬ (0 < a.re ∧ a.re < 1)) (hfix : nuZeta a = a) :
    IsRepellingFixedPoint nuZeta a := by
  have hzeta : riemannZeta a = 0 := by
    rcases hreg with hz | hderiv
    · exact hz
    · by_contra hz
      have hquot : riemannZeta a / (a * deriv riemannZeta a) = 0 := by
        have heq : a - riemannZeta a / (a * deriv riemannZeta a) = a := by
          simpa [nuZeta, nu] using hfix
        exact sub_eq_self.mp heq
      exact (div_ne_zero hz (mul_ne_zero ha0 hderiv)) hquot
  have hex : ∃ n : ℕ, a = -2 * (n + 1) := by
    by_contra hnone
    push Not at hnone
    exact hout (Kawahira.nontrivial_zero_mem_strip a hzeta hnone)
  obtain ⟨n, ha_neg⟩ := hex
  have horder : analyticOrderAt riemannZeta a = (1 : ℕ∞) := by
    rw [ha_neg]
    simpa using riemannZeta_trivial_zero_order_one n
  have han : AnalyticAt ℂ riemannZeta a :=
    analyticOn_riemannZeta a (by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using ha1)
  have hnu := Kawahira.nu_at_zero_of_order riemannZeta a 1 ha0 (by norm_num) han horder
  refine ⟨hfix, ?_⟩
  have hderiv_nu : deriv nuZeta a = 1 - a⁻¹ := by
    simpa [nuZeta] using hnu.2
  rw [hderiv_nu]
  have hrelt : a.re < 1 / 2 := by
    have hre := congrArg Complex.re ha_neg
    norm_num at hre
    have hn0 : (0 : ℝ) ≤ n := by positivity
    linarith
  have heq_iff := (Kawahira.norm_one_sub_inv a ha0).1
  have hlt_iff := (Kawahira.norm_one_sub_inv a ha0).2
  have hnotlt : ¬ ‖1 - a⁻¹‖ < 1 := by
    rw [hlt_iff]
    linarith
  rcases lt_trichotomy ‖1 - a⁻¹‖ 1 with hlt | heq | hgt
  · exact (hnotlt hlt).elim
  · exact (hrelt.ne (heq_iff.mp heq)).elim
  · exact hgt
