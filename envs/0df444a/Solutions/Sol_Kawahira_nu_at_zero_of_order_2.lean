-- Prove2me | solution 2 for Kawahira.nu_at_zero_of_order
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T21:52:07.195591+00:00
-- url     : https://prove2.me/submissions/afd3ba3b-b438-4648-a967-6a8ebd8560c2

import Definitions.Def_Kawahira_zeta

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace KawLoc

open Complex Topology Kawahira

/-- The local normal form of `g`, `g'`, `newton g` and `nu g` at a zero of order `k + 1`. -/
theorem local_form (g : ℂ → ℂ) (a : ℂ) (k : ℕ)
    (hg : AnalyticAt ℂ g a) (horder : analyticOrderAt g a = ((k + 1 : ℕ) : ℕ∞)) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h a ∧ h a ≠ 0 ∧
      (∀ᶠ z in 𝓝 a, g z = (z - a) ^ k * ((z - a) * h z)) ∧
      (∀ᶠ z in 𝓝 a, deriv g z
        = (z - a) ^ k * (((k : ℂ) + 1) * h z + (z - a) * deriv h z)) := by
  obtain ⟨h, hh, hh0, hgh⟩ := hg.analyticOrderAt_eq_natCast.1 horder
  refine ⟨h, hh, hh0, ?_, ?_⟩
  · filter_upwards [hgh] with z hz
    rw [hz, smul_eq_mul, pow_succ]
    ring
  · have hnear : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ h z := by
      filter_upwards [hh.eventually_analyticAt] with z hz
      exact hz.differentiableAt
    have heq : ∀ᶠ z in 𝓝 a, g =ᶠ[𝓝 z] fun w => (w - a) ^ (k + 1) * h w := by
      refine Filter.EventuallyEq.eventuallyEq_nhds ?_
      filter_upwards [hgh] with z hz
      rw [hz, smul_eq_mul]
    filter_upwards [hnear, heq] with z hz1 hz2
    rw [hz2.deriv_eq]
    have hp : HasDerivAt (fun w : ℂ => (w - a) ^ (k + 1)) (((k : ℂ) + 1) * (z - a) ^ k) z := by
      simpa using ((hasDerivAt_id z).sub_const a).fun_pow (k + 1)
    have hd : HasDerivAt (fun w : ℂ => (w - a) ^ (k + 1) * h w)
        (((k : ℂ) + 1) * (z - a) ^ k * h z + (z - a) ^ (k + 1) * deriv h z) z :=
      hp.mul hz1.hasDerivAt
    rw [hd.deriv]
    rw [pow_succ]
    ring


/-! ### The Newton map and the nu map at a zero of order `m` -/

theorem newton_at_zero_of_order (g : ℂ → ℂ) (a : ℂ) (m : ℕ) (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g a) (horder : analyticOrderAt g a = (m : ℕ∞)) :
    newton g a = a ∧ deriv (newton g) a = 1 - 1 / (m : ℂ) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨h, hh, hh0, hgf, hgd⟩ := local_form g a k hg horder
  set N : ℂ → ℂ := fun z => (z - a) * h z with hN
  set D : ℂ → ℂ := fun z => ((k : ℂ) + 1) * h z + (z - a) * deriv h z with hD
  have hNa : N a = 0 := by simp [hN]
  have hDa : D a = ((k : ℂ) + 1) * h a := by simp [hD]
  have hk0 : ((k : ℂ) + 1) ≠ 0 := by
    have hc : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast at hc
    exact hc
  have hDa0 : D a ≠ 0 := by rw [hDa]; exact mul_ne_zero hk0 hh0
  have hkey : newton g =ᶠ[𝓝 a] fun z => z - N z / D z := by
    filter_upwards [hgf, hgd] with z h1 h2
    rw [newton, h1, h2]
    rcases eq_or_ne z a with rfl | hz
    · simp [hN]
    · rw [mul_div_mul_left _ _ (pow_ne_zero k (sub_ne_zero.2 hz))]
  have hnewton : newton g a = a := by
    have hs := hkey.self_of_nhds
    rw [hs]
    simp [hNa]
  refine ⟨hnewton, ?_⟩
  have hhd : DifferentiableAt ℂ h a := hh.differentiableAt
  have hh'd : DifferentiableAt ℂ (deriv h) a := hh.deriv.differentiableAt
  have hNd : HasDerivAt N (h a) a := by
    have hx : HasDerivAt (fun y : ℂ => (y - a) * h y)
        (1 * h a + (a - a) * deriv h a) a :=
      ((hasDerivAt_id a).sub_const a).fun_mul hhd.hasDerivAt
    rw [hN]
    convert hx using 1
    ring
  have hDd : DifferentiableAt ℂ D a :=
    (hhd.const_mul _).add ((differentiableAt_id.sub_const a).mul hh'd)
  have hquot : HasDerivAt (fun z => N z / D z)
      ((h a * D a - N a * deriv D a) / D a ^ 2) a :=
    hNd.div hDd.hasDerivAt hDa0
  have hval : (h a * D a - N a * deriv D a) / D a ^ 2 = 1 / ((k : ℂ) + 1) := by
    rw [hNa, hDa]
    field_simp
    ring
  rw [hval] at hquot
  have hfinal : HasDerivAt (fun z => z - N z / D z) (1 - 1 / ((k : ℂ) + 1)) a := by
    have hx := (hasDerivAt_id a).fun_sub hquot
    simpa using hx
  rw [hkey.deriv_eq, hfinal.deriv]
  push_cast
  ring

theorem nu_at_zero_of_order (g : ℂ → ℂ) (a : ℂ) (m : ℕ) (ha : a ≠ 0) (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g a) (horder : analyticOrderAt g a = (m : ℕ∞)) :
    nu g a = a ∧ deriv (nu g) a = 1 - 1 / (m * a) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨h, hh, hh0, hgf, hgd⟩ := local_form g a k hg horder
  set N : ℂ → ℂ := fun z => (z - a) * h z with hN
  set E : ℂ → ℂ := fun z => z * (((k : ℂ) + 1) * h z + (z - a) * deriv h z) with hE
  have hNa : N a = 0 := by simp [hN]
  have hEa : E a = a * (((k : ℂ) + 1) * h a) := by simp [hE]
  have hk0 : ((k : ℂ) + 1) ≠ 0 := by
    have hc : ((k + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    push_cast at hc
    exact hc
  have hEa0 : E a ≠ 0 := by
    rw [hEa]; exact mul_ne_zero ha (mul_ne_zero hk0 hh0)
  have hkey : nu g =ᶠ[𝓝 a] fun z => z - N z / E z := by
    filter_upwards [hgf, hgd] with z h1 h2
    rw [nu, h1, h2]
    rcases eq_or_ne z a with rfl | hz
    · simp [hN]
    · rw [show z * ((z - a) ^ k * (((k : ℂ) + 1) * h z + (z - a) * deriv h z))
          = (z - a) ^ k * E z by rw [hE]; ring]
      rw [mul_div_mul_left _ _ (pow_ne_zero k (sub_ne_zero.2 hz))]
  have hnu : nu g a = a := by
    have hs := hkey.self_of_nhds
    rw [hs]
    simp [hNa]
  refine ⟨hnu, ?_⟩
  have hhd : DifferentiableAt ℂ h a := hh.differentiableAt
  have hh'd : DifferentiableAt ℂ (deriv h) a := hh.deriv.differentiableAt
  have hNd : HasDerivAt N (h a) a := by
    have hx : HasDerivAt (fun y : ℂ => (y - a) * h y)
        (1 * h a + (a - a) * deriv h a) a :=
      ((hasDerivAt_id a).sub_const a).fun_mul hhd.hasDerivAt
    rw [hN]
    convert hx using 1
    ring
  have hEd : DifferentiableAt ℂ E a :=
    differentiableAt_id.mul ((hhd.const_mul _).add ((differentiableAt_id.sub_const a).mul hh'd))
  have hquot : HasDerivAt (fun z => N z / E z)
      ((h a * E a - N a * deriv E a) / E a ^ 2) a :=
    hNd.div hEd.hasDerivAt hEa0
  have hval : (h a * E a - N a * deriv E a) / E a ^ 2 = 1 / (((k : ℂ) + 1) * a) := by
    rw [hNa, hEa]
    field_simp
    ring
  rw [hval] at hquot
  have hfinal : HasDerivAt (fun z => z - N z / E z) (1 - 1 / (((k : ℂ) + 1) * a)) a := by
    have hx := (hasDerivAt_id a).fun_sub hquot
    simpa using hx
  rw [hkey.deriv_eq, hfinal.deriv]
  push_cast
  ring

end KawLoc

open Complex Topology Kawahira in
theorem solution (g : ℂ → ℂ) (a : ℂ) (m : ℕ) (ha : a ≠ 0) (hm : 1 ≤ m)
    (hg : AnalyticAt ℂ g a) (horder : analyticOrderAt g a = (m : ℕ∞)) :
    nu g a = a ∧ deriv (nu g) a = 1 - 1 / (m * a) :=
  KawLoc.nu_at_zero_of_order g a m ha hm hg horder
