-- Prove2me | solution 1 for LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:53:30.382696+00:00
-- url     : https://prove2.me/submissions/007d4319-7110-4754-99b5-cc5f31f419a0

import Definitions.Def_KLS408915f_LevyStochCalc_Probability_DoobContinuous
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_Progressive
import Definitions.Def_KLS408915f_LevyStochCalc_Probability_ProgressiveCadlag
import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.Process.Adapted
import Theorems.Thm_MeasureTheory_maximal_ineq_Lp_408915f

section
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
variable [m0 : MeasurableSpace Ω] {μ : Measure Ω}
/-- The norm process of a Banach-valued martingale is a non-negative submartingale.
Internal lemma used to derive the Banach version of Doob's L^p inequality from the
real-valued case via Jensen (`MeasureTheory.norm_condExp_le`). -/
private lemma MeasureTheory.martingale_norm_submartingale
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → E} (hf : Martingale f 𝒢 μ) :
    Submartingale (fun n ω ↦ ‖f n ω‖) 𝒢 μ := by
  refine ⟨fun n ↦ continuous_norm.comp_stronglyMeasurable (hf.stronglyAdapted n),
          fun i j hij ↦ ?_, fun n ↦ (hf.integrable n).norm⟩
  have hcondExp : f i =ᵐ[μ] μ[f j | (𝒢 i : MeasurableSpace Ω)] := (hf.condExp_ae_eq hij).symm
  filter_upwards [hcondExp,
    norm_condExp_le (f := f j) (m := (𝒢 i : MeasurableSpace Ω)) (μ := μ)]
    with ω hω hjensen
  calc ‖f i ω‖ = ‖(μ[f j | (𝒢 i : MeasurableSpace Ω)]) ω‖ := by rw [hω]
    _ ≤ _ := hjensen
/-- Doob's L^p maximal inequality, Banach-valued martingale form.

For a Banach-valued martingale `f : ℕ → Ω → E` and `1 < p`,
`‖max_{k ≤ n} ‖f_k‖‖_{L^p} ≤ (p / (p - 1)) · ‖f_n‖_{L^p}`.

Derived from `MeasureTheory.maximal_ineq_Lp` by applying it to the non-negative
real-valued submartingale `‖f‖`. -/
theorem MeasureTheory.Martingale.eLpNorm_norm_runMax_le
    [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → E} {p : ℝ}
    (hf : Martingale f 𝒢 μ) (hp : 1 < p) (n : ℕ) :
    eLpNorm (fun ω ↦ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        (fun k ↦ ‖f k ω‖)) (ENNReal.ofReal p) μ
      ≤ ENNReal.ofReal (p / (p - 1)) * eLpNorm (f n) (ENNReal.ofReal p) μ := by
  have hsub := martingale_norm_submartingale hf
  have hbound := maximal_ineq_Lp_408915f hsub (fun _ _ ↦ norm_nonneg _) hp n
  rwa [eLpNorm_norm] at hbound
end
end
end

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/DoobContinuous.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
section
namespace LevyStochCalc
end LevyStochCalc
open LevyStochCalc
section
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc LevyStochCalc.Probability
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
/-- A martingale sampled along a monotone time map is a martingale for the sampled
filtration. -/
theorem LevyStochCalc.Probability.martingale_compMono {ι ι' : Type*} [Preorder ι] [Preorder ι']
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure Ω} {ℱ : Filtration ι' mΩ} {f : ι' → Ω → E}
    (hf : MeasureTheory.Martingale f ℱ μ) (τ : ι → ι') (hτ : Monotone τ) :
    MeasureTheory.Martingale (fun i => f (τ i)) (Filtration.compMono mΩ ℱ τ hτ) μ :=
  ⟨fun i => hf.1 (τ i), fun i j hij => hf.2 (τ i) (τ j) (hτ hij)⟩
theorem LevyStochCalc.Probability.dyadicTime_monotone {T : ℝ} (hT : 0 ≤ T) (n : ℕ) : Monotone (dyadicTime T n) := by
  intro k l hkl
  refine min_le_min ?_ le_rfl
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) hT
@[simp] theorem LevyStochCalc.Probability.dyadicTime_top {T : ℝ} (n : ℕ) :
    dyadicTime T n (2 ^ n) = T := by
  have h : ((2 ^ n : ℕ) : ℝ) * T / 2 ^ n = T := by
    push_cast
    field_simp
  rw [dyadicTime, h, min_self]
variable {M : ℝ → Ω → ℝ} {T : ℝ}
/-- The `L²` seminorm as a `lintegral`. -/
theorem LevyStochCalc.Probability.eLpNorm_two_eq {μ : Measure Ω} (f : Ω → ℝ) :
    eLpNorm f 2 μ = (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← ENNReal.rpow_natCast _ 2]
  norm_num
  simp [enorm_eq_nnnorm]
namespace LevyStochCalc.Probability
end LevyStochCalc.Probability
open LevyStochCalc.Probability in
/-- **Doob's `L²` maximal inequality at a dyadic level.** -/
theorem solution {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℝ mΩ} (hM : MeasureTheory.Martingale M ℱ μ) (hT : 0 ≤ T) (n : ℕ) :
    ∫⁻ ω, (‖LevyStochCalc.Probability.dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hsamp := LevyStochCalc.Probability.martingale_compMono hM (LevyStochCalc.Probability.dyadicTime T n) (LevyStochCalc.Probability.dyadicTime_monotone hT n)
  have hdoob := MeasureTheory.Martingale.eLpNorm_norm_runMax_le hsamp
    (by norm_num : (1 : ℝ) < 2) (2 ^ n)
  have hp : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by
    simp
  have hc : ENNReal.ofReal ((2 : ℝ) / (2 - 1)) = (2 : ℝ≥0∞) := by
    norm_num
  rw [hp, hc, LevyStochCalc.Probability.dyadicTime_top n] at hdoob
  have hlhs : eLpNorm (fun ω => (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
      fun k => ‖M (LevyStochCalc.Probability.dyadicTime T n k) ω‖) 2 μ = eLpNorm (LevyStochCalc.Probability.dyadicRunMax M T n) 2 μ := rfl
  rw [hlhs, LevyStochCalc.Probability.eLpNorm_two_eq, LevyStochCalc.Probability.eLpNorm_two_eq] at hdoob
  have hsq := ENNReal.rpow_le_rpow hdoob (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2),
    ← ENNReal.rpow_mul] at hsq
  norm_num at hsq
  calc ∫⁻ ω, (‖LevyStochCalc.Probability.dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ
      = (∫⁻ ω, (‖LevyStochCalc.Probability.dyadicRunMax M T n ω‖₊ : ℝ≥0∞) ^ 2 ∂μ) ^ (1 : ℝ) := by
        rw [ENNReal.rpow_one]
    _ ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
        simpa using hsq
