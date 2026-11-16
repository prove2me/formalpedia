-- Prove2me | solution 1 for Kyprianou.Ch01.gammaLaplacePositiveTimeAE
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T19:58:14.171883+00:00
-- url     : https://prove2.me/submissions/e269c71e-424c-41f9-a463-c306dc995e83

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- The Laplace transform of a positive-shape gamma marginal forces
    zero mass on the nonpositive half-line at every positive time. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (alpha beta : ℝ) (ha : 0 < alpha) (hb : 0 < beta)
    (hLaplace : ∀ (t : ℝ≥0) (q : ℝ), 0 ≤ q →
      Integrable (fun ω => Real.exp (-q * X t ω)) P ∧
      (∫ ω, Real.exp (-q * X t ω) ∂P) =
        (alpha / (alpha + q)) ^ (beta * (t : ℝ))) :
    ∀ t : ℝ≥0, 0 < t → ∀ᵐ ω ∂P, 0 < X t ω := by
  intro t ht
  let A : Set Ω := {ω | X t ω ≤ 0}
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hk : 0 < beta * (t : ℝ) := mul_pos hb htR
  have hratio (n : ℕ) :
      alpha / (alpha + alpha * (n : ℝ)) = ((n : ℝ) + 1)⁻¹ := by
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    have hd : alpha + alpha * (n : ℝ) ≠ 0 := by positivity
    field_simp [ne_of_gt ha, hn, hd]
    ring
  have hbound (n : ℕ) :
      P A ≤ ENNReal.ofReal (((n : ℝ) + 1) ^ (-(beta * (t : ℝ)))) := by
    have hq : 0 ≤ alpha * (n : ℝ) := mul_nonneg ha.le (Nat.cast_nonneg n)
    have hi := hLaplace t (alpha * (n : ℝ)) hq
    have hnonneg : 0 ≤ᵐ[P] (fun ω => Real.exp (-(alpha * (n : ℝ)) * X t ω)) :=
      Filter.Eventually.of_forall (fun ω => (Real.exp_pos _).le)
    have hmk : P A ≤ ENNReal.ofReal
        (∫ ω, Real.exp (-(alpha * (n : ℝ)) * X t ω) ∂P) := by
      apply hi.1.measure_le_integral hnonneg
      intro ω hω
      have hx : X t ω ≤ 0 := hω
      have hc : 0 ≤ -(alpha * (n : ℝ)) * X t ω :=
        mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hq) hx
      exact Real.one_le_exp_iff.mpr hc
    calc
      P A ≤ ENNReal.ofReal ((alpha / (alpha + alpha * (n : ℝ))) ^
          (beta * (t : ℝ))) := by simpa only [hi.2] using hmk
      _ = ENNReal.ofReal (((n : ℝ) + 1) ^ (-(beta * (t : ℝ)))) := by
        rw [hratio]
        rw [← Real.rpow_neg_eq_inv_rpow]
  have hlimitBase :
      Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hlimitReal :
      Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(beta * (t : ℝ))))
        atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hk).comp hlimitBase
  have hlimit :
      Tendsto
        (fun n : ℕ => ENNReal.ofReal (((n : ℝ) + 1) ^ (-(beta * (t : ℝ)))))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlimitReal
  have hzero : P A = 0 := by
    apply le_antisymm (ge_of_tendsto' hlimit (fun n => hbound n))
    exact zero_le
  have hae : ∀ᵐ ω ∂P, ¬ (X t ω ≤ 0) := by
    apply ae_iff.mpr
    simpa only [not_not] using hzero
  filter_upwards [hae] with ω hw
  exact lt_of_not_ge hw
