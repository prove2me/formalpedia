-- Prove2me | solution 1 for Kawahira.logQuotient_hasDerivAt_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:48:23.008517+00:00
-- url     : https://prove2.me/submissions/f6a1a9a8-f647-46bf-ad1e-fab6e3fa0e4e

import Definitions.Def_Kawahira_zeta

open Complex Topology Filter

theorem solution
    (g q : ℂ → ℂ) (a : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (hq : AnalyticAt ℂ q a) (hqa : q a ≠ 0)
    (hgq : g =ᶠ[𝓝 a] fun z => (z - a) ^ m * q z) :
    g a / deriv g a = 0 ∧
      HasDerivAt (fun z => g z / deriv g z) (1 / (m : ℂ)) a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  have hgq' : g =ᶠ[𝓝 a] fun z => (z - a) ^ (k + 1) * q z := by
    simpa only [Nat.succ_eq_add_one] using hgq
  have hga : g a = 0 := by
    simpa using hgq'.self_of_nhds
  have hdg : deriv g =ᶠ[𝓝 a] fun z =>
      ((k + 1 : ℕ) : ℂ) * (z - a) ^ k * q z + (z - a) ^ (k + 1) * deriv q z := by
    filter_upwards [hgq'.deriv, hq.eventually_analyticAt] with z hz hzq
    rw [hz]
    rw [deriv_fun_mul (by fun_prop) hzq.differentiableAt, deriv_fun_pow (by fun_prop)]
    simp [pow_succ]
  let R : ℂ → ℂ := fun z =>
    ((z - a) * q z) /
      (((k + 1 : ℕ) : ℂ) * q z + (z - a) * deriv q z)
  have hratio : (fun z => g z / deriv g z) =ᶠ[𝓝 a] R := by
    filter_upwards [hgq', hdg] with z hgz hdz
    simp only [R]
    rw [hgz, hdz]
    by_cases hza : z = a
    · simp [hza]
    · have hne : z - a ≠ 0 := sub_ne_zero.mpr hza
      calc
        (z - a) ^ (k + 1) * q z /
              (↑(k + 1) * (z - a) ^ k * q z + (z - a) ^ (k + 1) * deriv q z) =
            (z - a) ^ k * ((z - a) * q z) /
              ((z - a) ^ k * (↑(k + 1) * q z + (z - a) * deriv q z)) := by
                congr 1 <;> rw [pow_succ] <;> ring
        _ = (z - a) * q z / (↑(k + 1) * q z + (z - a) * deriv q z) :=
          mul_div_mul_left _ _ (pow_ne_zero _ hne)
  have hden : (((k + 1 : ℕ) : ℂ) * q a + (a - a) * deriv q a) ≠ 0 := by
    simpa using
      mul_ne_zero (Nat.cast_ne_zero.mpr (by omega : k + 1 ≠ 0) : ((k + 1 : ℕ) : ℂ) ≠ 0) hqa
  have hR : HasDerivAt R (1 / ((k + 1 : ℕ) : ℂ)) a := by
    have hNdiff : DifferentiableAt ℂ (fun z : ℂ => (z - a) * q z) a := by
      fun_prop
    have hN : HasDerivAt (fun z => (z - a) * q z) (q a) a := by
      apply hNdiff.hasDerivAt.congr_deriv
      rw [deriv_fun_mul (by fun_prop) hq.differentiableAt]
      simp
    have hD : DifferentiableAt ℂ
        (fun z => ((k + 1 : ℕ) : ℂ) * q z + (z - a) * deriv q z) a := by
      fun_prop
    have hquot := hN.div hD.hasDerivAt hden
    change HasDerivAt
      ((fun z : ℂ => (z - a) * q z) /
        fun z : ℂ => ((k + 1 : ℕ) : ℂ) * q z + (z - a) * deriv q z)
      (1 / ((k + 1 : ℕ) : ℂ)) a
    apply hquot.congr_deriv
    simp only [sub_self, zero_mul, add_zero]
    field_simp [hqa]
    ring
  constructor
  · simp [hga]
  · exact hratio.hasDerivAt_iff.mpr hR
