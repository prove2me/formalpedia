-- Prove2me | solution 1 for Kawahira.nu_at_zero_of_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:48:37.127196+00:00
-- url     : https://prove2.me/submissions/c03492b1-ac35-40d5-b0d5-179085042e31

import Definitions.Def_Kawahira_zeta
import Theorems.Thm_Kawahira_logQuotient_hasDerivAt_of_factor

open Complex Topology
open Kawahira

theorem solution (g : ℂ → ℂ) (a : ℂ) (m : ℕ) (ha : a ≠ 0) (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g a) (horder : analyticOrderAt g a = (m : ℕ∞)) :
    nu g a = a ∧ deriv (nu g) a = 1 - 1 / (m * a) := by
  obtain ⟨q, hq, hqa, hgq⟩ := hg.analyticOrderAt_eq_natCast.mp horder
  have hgq' : g =ᶠ[𝓝 a] fun z => (z - a) ^ m * q z := by
    filter_upwards [hgq] with z hz
    simpa [smul_eq_mul] using hz
  obtain ⟨hzero, hderiv⟩ :=
    Kawahira.logQuotient_hasDerivAt_of_factor g q a m hm hq hqa hgq'
  have hratio : (fun z => g z / (z * deriv g z)) =
      fun z => (g z / deriv g z) / z := by
    funext z
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdiv0 := hderiv.div (hasDerivAt_id a) ha
  simp only [id_eq] at hdiv0
  have hdiv : HasDerivAt (fun z => (g z / deriv g z) / z) (1 / (m * a)) a := by
    apply hdiv0.congr_deriv
    simp only [hzero, zero_mul, sub_zero]
    field_simp [hm0, ha]
  have hnu : nu g = fun z => z - (g z / deriv g z) / z := by
    funext z
    rw [nu, congrFun hratio z]
  constructor
  · rw [hnu]
    simp [hzero]
  · rw [hnu]
    exact ((hasDerivAt_id a).sub hdiv).deriv
