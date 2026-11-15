-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSketch.smoothingError_negligible
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:24:56.465412+00:00
-- url     : https://prove2.me/submissions/4d2cb77b-87db-400e-92a6-501b9eabd464

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
set_option maxHeartbeats 200000
open QAlgorithms.Complexity
open InfoLossLAR.WorstCase
open Filter
open scoped BigOperators Classical

namespace InfoLossLAR.WorstCase.RegevSketch

private theorem smoothingError_pos (dimension : ℕ) : 0 < smoothingError dimension := by
  unfold smoothingError
  positivity

/-- The body is the checked integer-order proof for fixedSmoothingError,
with only the definition name changed to the identical sketch schedule. -/
private theorem integer_order_bound : ∀ order : ℕ,∀ᶠ dimension : ℕ in atTop,
    |smoothingError dimension| ≤ 1/(dimension : ℝ)^order := by
  intro order
  refine eventually_atTop.mpr ⟨2^order,?_⟩
  intro dimension hdimension
  let bits := Nat.size (dimension+2)
  have hbits : order ≤ bits := (Nat.lt_size.mpr (hdimension.trans (by omega : dimension ≤ dimension+2))).le
  have hd : (dimension : ℝ) ≤ (2 : ℝ)^bits := by
    exact_mod_cast (le_trans (by omega : dimension ≤ dimension+2) (Nat.lt_size_self (dimension+2)).le)
  have hpower : (dimension : ℝ)^order ≤ (2 : ℝ)^(bits^2) := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg dimension) hd order
    rw [←pow_mul] at h
    exact h.trans (pow_le_pow_right₀ (by norm_num) (by nlinarith [Nat.mul_le_mul_left bits hbits]))
  rw [abs_of_pos (smoothingError_pos dimension)]
  exact one_div_le_one_div_of_le (by
    have hpositive : 0 < dimension := (pow_pos (by decide) order).trans_le hdimension
    positivity) hpower

end InfoLossLAR.WorstCase.RegevSketch
open InfoLossLAR.WorstCase.RegevSketch

/-- Existing checked platform-neglect conversion applied to the identical
fixed schedule; no lattice or sampler existence statement is assumed. -/
theorem solution : InfoLossLAR.WorstCase.Negligible smoothingError := by
  refine ⟨fun dimension => (smoothingError_pos dimension).le,?_⟩
  intro c hc
  let order : ℕ := ⌈c⌉₊
  have horder : c ≤ (order : ℝ) := Nat.le_ceil c
  obtain ⟨cutoff,hcutoff⟩ := eventually_atTop.1 ((integer_order_bound order).and (eventually_ge_atTop 1))
  refine ⟨cutoff,?_⟩
  intro n hn
  obtain ⟨he,hne⟩ := hcutoff n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hne
  calc
    smoothingError n ≤ 1/(n : ℝ)^order := (le_abs_self _).trans he
    _=(n : ℝ)^(-(order : ℝ)) := by
      rw [Real.rpow_neg (by positivity),Real.rpow_natCast,one_div]
    _ ≤ (n : ℝ)^(-c) := Real.rpow_le_rpow_of_exponent_le hnR (neg_le_neg horder)
