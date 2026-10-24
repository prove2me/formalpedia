-- Prove2me | solution 1 for MeasureTheory.maximal_ineq_Lp_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:52:42.512984+00:00
-- url     : https://prove2.me/submissions/ebc5e394-b6e5-4d52-aea2-4e4a17839471

import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping
import Theorems.Thm_MeasureTheory_holder_step_408915f
import Theorems.Thm_MeasureTheory_runMax_pow_lintegral_lt_top_408915f

/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
-- Vendored from https://github.com/raphaelrrcoelho/formal-mathfin at commit 784a8311f75a1519a23717856df9982bd6a9a370 (upstream path MathFin/Foundations/DoobLpMaximalInequality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
section
open ProbabilityTheory ENNReal Filter Set Finset
open scoped NNReal
section
namespace MeasureTheory
end MeasureTheory
open MeasureTheory
variable {Ω : Type*}
private lemma MeasureTheory.runMax_nonneg {f : ℕ → Ω → ℝ} (hnonneg : ∀ n ω, 0 ≤ f n ω) (n : ℕ) (ω : Ω) :
    0 ≤ MeasureTheory.runMax f n ω :=
  le_trans (hnonneg 0 ω)
    (Finset.le_sup' (f := fun k ↦ f k ω) (Finset.mem_range.mpr (Nat.succ_pos n)))
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}
/-- Conversion lemma: for a non-negative `f : Ω → ℝ` and `1 < p`,
    `eLpNorm f (ofReal p) μ = (∫⁻ ω, ofReal(f ω ^ p) ∂μ)^(1/p)`. -/
private lemma MeasureTheory.eLpNorm_eq_lintegral_ofReal_pow
    {f : Ω → ℝ} (hf_nn : ∀ ω, 0 ≤ f ω) {p : ℝ} (hp : 1 < p) :
    eLpNorm f (ENNReal.ofReal p) μ
      = (∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ) ^ (1 / p) := by
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_ne_zero : (ENNReal.ofReal p) ≠ 0 := by
    simp [hp_pos]
  have hp_ne_top : (ENNReal.ofReal p) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp_ne_zero hp_ne_top]
  rw [ENNReal.toReal_ofReal hp_pos.le]
  congr 1
  apply lintegral_congr_ae
  filter_upwards with ω
  have : ‖f ω‖ₑ = ENNReal.ofReal (f ω) := by
    rw [Real.enorm_eq_ofReal (hf_nn ω)]
  rw [this, ENNReal.ofReal_rpow_of_nonneg (hf_nn ω) hp_pos.le]
namespace MeasureTheory
end MeasureTheory
open MeasureTheory in
/-- Doob's L^p maximal inequality for discrete-time non-negative submartingales.

For a non-negative submartingale `f : ℕ → Ω → ℝ` and `1 < p`, the L^p norm
of the running maximum `f*_n(ω) = max_{k ≤ n} f_k(ω)` is bounded by
`(p / (p - 1))` times the L^p norm of `f_n`:

  `‖f*_n‖_{L^p} ≤ (p / (p - 1)) · ‖f_n‖_{L^p}`.

This is the strong-type companion to `MeasureTheory.maximal_ineq`. The proof
combines a layer-cake decomposition, the weak-type maximal inequality, Fubini,
Hölder's inequality, and a truncation argument to handle the case where the
left-hand side could a priori be infinite. -/
theorem solution
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ f k ω)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) *
          eLpNorm (f n) (ENNReal.ofReal p) μ := by
  -- `Finset.sup'` is definitionally `runMax f n`.
  change eLpNorm (MeasureTheory.runMax f n) (ENNReal.ofReal p) μ ≤ _
  rw [eLpNorm_eq_lintegral_ofReal_pow (runMax_nonneg hnonneg n) hp,
      eLpNorm_eq_lintegral_ofReal_pow (hnonneg n) hp]
  set A : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ p) ∂μ
  set B : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal ((f n ω) ^ p) ∂μ
  set C : ℝ≥0∞ := ENNReal.ofReal (p / (p - 1)) with hC_def
  have hbound : A ≤ C * B ^ (1 / p) * A ^ ((p - 1) / p) := MeasureTheory.holder_step_408915f hsub hnonneg hp n
  have hp_pos : 0 < p := lt_trans zero_lt_one hp
  have hp_inv_pos : 0 < 1 / p := by positivity
  have hpm1_p_pos : 0 < (p - 1) / p := div_pos (by linarith) hp_pos
  -- Degenerate cases first.
  by_cases hA0 : A = 0
  · rw [hA0, ENNReal.zero_rpow_of_pos hp_inv_pos]
    exact bot_le
  by_cases hAtop : A = ⊤
  · by_cases hBtop : B = ⊤
    · -- Both sides `⊤` since `C ≠ 0`.
      have hC_ne_zero : C ≠ 0 := by
        rw [hC_def]
        exact (ENNReal.ofReal_pos.mpr (div_pos hp_pos (by linarith))).ne'
      rw [hAtop, hBtop, ENNReal.top_rpow_of_pos hp_inv_pos, ENNReal.mul_top hC_ne_zero]
    · -- `A = ⊤` while `B < ⊤` contradicts the finiteness lemma.
      exact absurd hAtop (MeasureTheory.runMax_pow_lintegral_lt_top_408915f hsub hnonneg hp n
        (lt_of_le_of_ne le_top hBtop)).ne
  -- Main case `0 < A < ⊤`: divide `hbound` by `A^{(p-1)/p}`.
  have hApm1_ne_zero : A ^ ((p - 1) / p) ≠ 0 :=
    fun h ↦ hA0 (ENNReal.rpow_eq_zero_iff_of_pos hpm1_p_pos |>.mp h)
  have hApm1_ne_top : A ^ ((p - 1) / p) ≠ ⊤ :=
    fun h ↦ hAtop ((ENNReal.rpow_eq_top_iff_of_pos hpm1_p_pos).mp h)
  have h_sum : (1 : ℝ) / p + (p - 1) / p = 1 := by
    rw [← add_div, show (1 : ℝ) + (p - 1) = p by ring, div_self hp_pos.ne']
  have h_split : A ^ (1 / p) = A / A ^ ((p - 1) / p) := by
    rw [eq_div_iff hApm1_ne_zero hApm1_ne_top, mul_comm,
        ← ENNReal.rpow_add_of_nonneg (1/p) ((p-1)/p) hp_inv_pos.le hpm1_p_pos.le,
        h_sum, ENNReal.rpow_one]
  rw [h_split, ENNReal.div_le_iff hApm1_ne_zero hApm1_ne_top]
  exact hbound
