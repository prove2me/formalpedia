-- Prove2me | solution 1 for Kyprianou.Ch04.rightContinuousTimeMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:52:44.912101+00:00
-- url     : https://prove2.me/submissions/3690a435-e1f3-4803-a5d7-6d426b008813

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A right-continuous real path on nonnegative time is Borel measurable. -/
theorem solution (U : NNReal → ℝ)
    (hU : ∀ t : NNReal, ContinuousWithinAt U (Ici t) t) : Measurable U := by
  let r (n : ℕ) (t : NNReal) := (⌈(t : ℝ) * (n : ℝ)⌉₊ : NNReal) / (n : NNReal)
  apply measurable_of_tendsto_metrizable (f := fun n t => U (r n t))
  · intro n
    exact (measurable_of_countable (fun k : ℕ => U ((k : NNReal) / (n : NNReal)))).comp
      ((NNReal.continuous_coe.measurable.mul_const (n : ℝ)).nat_ceil)
  apply tendsto_pi_nhds.mpr
  intro t
  have hlim : Tendsto (fun n : ℕ => r n t) atTop (𝓝 t) := by
    apply NNReal.tendsto_coe.mp
    simpa [r, Function.comp_def] using (tendsto_nat_ceil_mul_div_atTop (R := ℝ) t.coe_nonneg).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hwithin : Tendsto (fun n : ℕ => r n t) atTop (𝓝[Ici t] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hlim, ?_⟩
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    change t ≤ r n t
    apply NNReal.coe_le_coe.mp
    simp only [r, NNReal.coe_div, NNReal.coe_natCast]
    apply (le_div_iff₀ (by exact_mod_cast (show 0 < n from by omega) : 0 < (n : ℝ))).2
    exact Nat.le_ceil ((t : ℝ) * (n : ℝ))
  exact (show Tendsto U (𝓝[Ici t] t) (𝓝 (U t)) from hU t).comp hwithin
