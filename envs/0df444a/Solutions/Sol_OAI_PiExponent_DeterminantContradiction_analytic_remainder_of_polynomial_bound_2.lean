-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.analytic_remainder_of_polynomial_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T18:05:53.997967+00:00
-- url     : https://prove2.me/submissions/69591644-61ae-40d4-9715-94a418f9875a

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib

section

open Filter Topology

namespace PiL24

/-- abstract version -/
theorem rem_tendsto (r : ℝ → ℕ) (m : ℕ) (v0 k : ℝ) (hv0 : 0 < v0)
    (hbound : ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop, 0 < (r H : Real) ∧ (r H : Real) ≤ C * (H + 1) ^ (m + 1)) :
    Tendsto (fun H : Real => (Real.log (r H : Real) + k +
      Real.log ((H + 1) ^ (2 * m) * (H / v0 + 1))) / H) atTop (𝓝 0) := by
  obtain ⟨C, hC, hev⟩ := hbound
  set A := |k| + |Real.log C| + Real.log (1 / v0 + 1)
  set B : ℝ := 3 * m + 2
  have hlog : Tendsto (fun H : ℝ => Real.log (H + 1) / H) atTop (𝓝 0) := by
    have h1 := Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
    have h2 : Tendsto (fun H : ℝ => H + 1) atTop atTop := tendsto_atTop_add_const_right _ _ tendsto_id
    refine (h1.comp h2).congr' ?_
    filter_upwards with H
    simp
  have hg : Tendsto (fun H : ℝ => A * H⁻¹ + B * (Real.log (H + 1) / H)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.const_mul A).add (hlog.const_mul B)
    simpa using this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with H ⟨hr0, hrC⟩ hH
  have hH0 : 0 < H := by linarith
  have hr1 : (1 : ℝ) ≤ r H := by
    have : 0 < r H := by exact_mod_cast hr0
    exact_mod_cast this
  have hL0 : 0 ≤ Real.log (H + 1) := Real.log_nonneg (by linarith)
  have hlr0 : 0 ≤ Real.log (r H : ℝ) := Real.log_nonneg hr1
  have hlr : Real.log (r H : ℝ) ≤ Real.log C + (m + 1) * Real.log (H + 1) := by
    calc Real.log (r H : ℝ) ≤ Real.log (C * (H + 1) ^ (m + 1)) := Real.log_le_log (by linarith) hrC
      _ = _ := by rw [Real.log_mul hC.ne' (by positivity), Real.log_pow]; push_cast; ring
  have hq1 : (1 : ℝ) ≤ (H + 1) ^ (2 * m) := one_le_pow₀ (by linarith)
  have hq2 : (1 : ℝ) ≤ H / v0 + 1 := by have := div_nonneg hH0.le hv0.le; linarith
  have hq0 : 0 ≤ Real.log ((H + 1) ^ (2 * m) * (H / v0 + 1)) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1 hq2)
  have hq : Real.log ((H + 1) ^ (2 * m) * (H / v0 + 1)) ≤
      2 * m * Real.log (H + 1) + (Real.log (1 / v0 + 1) + Real.log (H + 1)) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have : Real.log (H / v0 + 1) ≤ Real.log ((1 / v0 + 1) * (H + 1)) := by
      apply Real.log_le_log (by positivity)
      have : H / v0 = (1 / v0) * H := by ring
      nlinarith [div_pos one_pos hv0]
    rw [Real.log_mul (by positivity) (by positivity)] at this
    push_cast; linarith
  have hlv : 0 ≤ Real.log (1 / v0 + 1) := Real.log_nonneg (by have := div_pos one_pos hv0; linarith)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hH0, div_le_iff₀ hH0]
  have hexp : (A * H⁻¹ + B * (Real.log (H + 1) / H)) * H = A + B * Real.log (H + 1) := by
    field_simp
  rw [hexp, abs_le]
  have hk := abs_nonneg k
  have hkl := neg_abs_le k
  have hkr := le_abs_self k
  have hCl := neg_abs_le (Real.log C)
  have hCr := le_abs_self (Real.log C)
  constructor
  · simp only [A, B]
    nlinarith
  · simp only [A, B]
    nlinarith

theorem main {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu)
    (hbound : ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop, 0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ∧ (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1)) :
    Tendsto (fun H : Real => (Real.log (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) + Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2)) + Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H) atTop (𝓝 0) := by
  have := rem_tendsto (fun H => OAI.PiExponent.DeterminantContradiction.actualRowCount d H) d.m (d.v0 : ℝ)
    (Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2))) d.v0_pos hbound
  refine this.congr' (Eventually.of_forall fun H => ?_)
  simp only [add_sub_assoc]

end PiL24

end

open OAI OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology

theorem solution {nu : Real} (d : OAI.PiExponent.DeterminantContradiction.FixedData nu) (hbound : ∃ C : Real, 0 < C ∧ ∀ᶠ H : Real in atTop, 0 < (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ∧ (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) ≤ C * (H + 1) ^ (d.m + 1)) : Tendsto (fun H : Real => (Real.log (OAI.PiExponent.DeterminantContradiction.actualRowCount d H : Real) + Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2)) + Real.log ((H + 1) ^ (2 * d.m) * (H / (d.v0 : Real) + 1))) / H) atTop (𝓝 0) := by
  apply PiL24.main <;> assumption
