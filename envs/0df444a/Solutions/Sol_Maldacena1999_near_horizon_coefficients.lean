-- Prove2me | solution 1 for Maldacena1999.near_horizon_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T12:23:05.571843+00:00
-- url     : https://prove2.me/submissions/70c1e57e-0498-4280-8e58-23f345b244bb

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

lemma malda_sqrt_harm_mul (g : ℝ) (N : ℕ) (U : ℝ) (hU : 0 < U) (a : ℝ) (ha : 0 < a) :
    Real.sqrt (Maldacena1999.harmonicFn g N a (a * U)) * a =
      Real.sqrt (a ^ 2 + 4 * Real.pi * g * N / U ^ 4) := by
  unfold Maldacena1999.harmonicFn
  rw [← Real.sqrt_sq ha.le, ← Real.sqrt_mul' _ (sq_nonneg a), Real.sqrt_sq ha.le]
  congr 1
  field_simp

lemma malda_tendsto_H (c : ℝ) :
    Tendsto (fun a : ℝ => Real.sqrt (a ^ 2 + c)) (𝓝[>] 0) (𝓝 (Real.sqrt c)) := by
  have hc : Continuous (fun a : ℝ => Real.sqrt (a ^ 2 + c)) := by fun_prop
  have := hc.tendsto 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at this
  exact this.mono_left nhdsWithin_le_nhds

open Maldacena1999 Filter Topology in
theorem solution (g : ℝ) (hg : 0 < g) (N : ℕ) (hN : 0 < N)
    (U : ℝ) (hU : 0 < U) :
    Tendsto (fun α' : ℝ => 1 / Real.sqrt (harmonicFn g N α' (α' * U)) / α')
        (𝓝[>] 0) (𝓝 (U ^ 2 / Real.sqrt (4 * Real.pi * g * N))) ∧
    Tendsto (fun α' : ℝ => Real.sqrt (harmonicFn g N α' (α' * U)) * α' ^ 2 / α')
        (𝓝[>] 0) (𝓝 (Real.sqrt (4 * Real.pi * g * N) / U ^ 2)) ∧
    Tendsto (fun α' : ℝ => Real.sqrt (harmonicFn g N α' (α' * U)) * (α' * U) ^ 2 / α')
        (𝓝[>] 0) (𝓝 (Real.sqrt (4 * Real.pi * g * N))) := by
  have hc : 0 < 4 * Real.pi * g * N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hU4 : Real.sqrt (U ^ 4) = U ^ 2 := by
    rw [show U ^ 4 = (U ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hlim0 : Real.sqrt (4 * Real.pi * g * N / U ^ 4) =
      Real.sqrt (4 * Real.pi * g * N) / U ^ 2 := by
    rw [Real.sqrt_div' _ (by positivity : (0:ℝ) ≤ U ^ 4), hU4]
  have hT := malda_tendsto_H (4 * Real.pi * g * N / U ^ 4)
  rw [hlim0] at hT
  have hsc : 0 < Real.sqrt (4 * Real.pi * g * N) := Real.sqrt_pos.2 hc
  have hev : ∀ᶠ a in 𝓝[>] (0:ℝ), 0 < a := self_mem_nhdsWithin
  refine ⟨?_, ?_, ?_⟩
  · have h2 := hT.inv₀ (by positivity : Real.sqrt (4 * Real.pi * g * N) / U ^ 2 ≠ 0)
    rw [show U ^ 2 / Real.sqrt (4 * Real.pi * g * N) =
      (Real.sqrt (4 * Real.pi * g * N) / U ^ 2)⁻¹ by rw [inv_div]]
    refine h2.congr' ?_
    filter_upwards [hev] with a ha
    have e := malda_sqrt_harm_mul g N U hU a ha
    rw [div_div, e, one_div]
  · refine hT.congr' ?_
    filter_upwards [hev] with a ha
    have e := malda_sqrt_harm_mul g N U hU a ha
    rw [← e]
    generalize Real.sqrt (harmonicFn g N a (a * U)) = s
    field_simp
  · have h3 := hT.mul_const (U ^ 2)
    rw [div_mul_cancel₀ _ (by positivity)] at h3
    refine h3.congr' ?_
    filter_upwards [hev] with a ha
    have e := malda_sqrt_harm_mul g N U hU a ha
    rw [← e]
    generalize Real.sqrt (harmonicFn g N a (a * U)) = s
    field_simp
