-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.integral_sq_weighted_polarQuadVarSum_le_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:35:46.438246+00:00
-- url     : https://prove2.me/submissions/4c6fcf31-15a6-47ee-8dbf-8275461f7627

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_PolarisedQuadVar
import Theorems.Thm_LevyStochCalc_Brownian_Ito_condExp_polarQuadVarIncrement_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_integral_sq_polarQuadVarIncrement_le_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_memLp_two_polarQuadVarIncrement_readable
import Theorems.Thm_LevyStochCalc_Brownian_Ito_stronglyMeasurable_polarQuadVarIncrement_readable
import Theorems.Thm_LevyStochCalc_Probability_integral_sq_sum_of_condExp_eq_zero_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/PolarisedQuadVar.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
section Polarised
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂MeasureTheory.MeasureSpace.volume ∂P < ⊤)
section Bounds
variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)
include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- **Second moment of a weighted sum of compensated products.** The compensated products are
martingale differences, so the weighted sum's second moment is controlled by the sum of the
squared cell lengths. -/
theorem solution
    (t : ℕ → ℝ) (h0 : 0 ≤ t 0) (ht : ∀ k, t k < t (k + 1))
    (g : ℕ → Ω → ℝ)
    (hg : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (t k)) (g k))
    {D : ℝ} (hD0 : 0 ≤ D) (hgD : ∀ (k : ℕ) (ω : Ω), |g k ω| ≤ D) (N : ℕ) :
    ∫ ω, (∑ i ∈ Finset.range N, g i ω
        * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t i) (t (i + 1)) ω) ^ 2 ∂P
      ≤ D ^ 2 * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
        * ∑ i ∈ Finset.range N, (t (i + 1) - t i) ^ 2 := by
  have htmono : StrictMono t := strictMono_nat_of_lt_succ ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => h0.trans (htmono.monotone (Nat.zero_le k))
  set 𝒢 : ℕ → MeasurableSpace Ω := fun k => ℱ.rightCont (t k) with h𝒢
  have h𝒢le : ∀ k, 𝒢 k ≤ ‹MeasurableSpace Ω› := fun k => ℱ.rightCont.le (t k)
  have h𝒢mono : Monotone 𝒢 := fun p q hpq => ℱ.rightCont.mono (htmono.monotone hpq)
  set Y : ℕ → Ω → ℝ := fun k ω =>
    g k ω * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t k) (t (k + 1)) ω
    with hY
  have hζmem : ∀ k, MemLp
      (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t k) (t (k + 1))) 2 P :=
    fun k => LevyStochCalc.Brownian.Ito.memLp_two_polarQuadVarIncrement_readable W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa hC0 hCH₁ hCH₂ (ht0 k) (ht k)
  have hgmeas : ∀ k, Measurable (g k) := fun k => ((hg k).mono (h𝒢le k)).measurable
  have hYmem : ∀ k, MemLp (Y k) 2 P := by
    intro k
    refine MeasureTheory.MemLp.mono ((hζmem k).const_mul D)
      ((hgmeas k).aestronglyMeasurable.mul (hζmem k).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_right (hgD k ω) (abs_nonneg _)
  have hYmeas : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _ (𝒢 (k + 1)) (Y k) := fun k =>
    ((hg k).mono (h𝒢mono (Nat.le_succ k))).mul
      (LevyStochCalc.Brownian.Ito.stronglyMeasurable_polarQuadVarIncrement_readable W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (ht k).le)
  have hYcond : ∀ k, P[Y k | 𝒢 k] =ᵐ[P] 0 := by
    intro k
    have hprod : Integrable (g k
        * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t k) (t (k + 1))) P :=
      (hYmem k).integrable (by norm_num)
    have hkey := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := 𝒢 k) (hg k)
      hprod ((hζmem k).integrable (by norm_num))
    have hfun : Y k = g k
        * LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t k) (t (k + 1)) := rfl
    rw [hfun]
    filter_upwards [hkey, LevyStochCalc.Brownian.Ito.condExp_polarQuadVarIncrement_readable W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa hC0 hCH₁ hCH₂ (ht0 k) (ht k)] with ω hω hω'
    rw [hω, Pi.mul_apply, hω', Pi.zero_apply, mul_zero]
  rw [LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero_readable 𝒢 h𝒢le h𝒢mono Y hYmem
    hYmeas hYcond N]
  have hterm : ∀ i ∈ Finset.range N, ∫ ω, (Y i ω) ^ 2 ∂P
      ≤ D ^ 2 * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
        * (t (i + 1) - t i) ^ 2 := by
    intro i _
    obtain ⟨hζint, hζle⟩ := LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le_readable W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂
      hq₁ hq₂ hma hpa hqa hC0 hCH₁ hCH₂ (ht0 i) (ht i)
    have hYint : Integrable (fun ω => (Y i ω) ^ 2) P := by
      have hfun : (fun ω => (Y i ω) ^ 2) = Y i * Y i := by funext ω; rw [pow_two]; rfl
      rw [hfun]
      exact (hYmem i).integrable_mul (hYmem i)
    have hstep : ∫ ω, (Y i ω) ^ 2 ∂P ≤ D ^ 2 * ∫ ω,
        (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t i) (t (i + 1)) ω) ^ 2
          ∂P := by
      have hle : ∫ ω, (Y i ω) ^ 2 ∂P ≤ ∫ ω, D ^ 2 *
          (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ (t i) (t (i + 1)) ω) ^ 2
            ∂P := by
        refine MeasureTheory.integral_mono hYint (hζint.const_mul _) fun ω => ?_
        have hgi : (g i ω) ^ 2 ≤ D ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (g i ω)) (hgD i ω) 2
          rwa [← abs_pow, abs_of_nonneg (sq_nonneg (g i ω))] at h
        have hsq : (Y i ω) ^ 2 = (g i ω) ^ 2 *
            (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
              (t i) (t (i + 1)) ω) ^ 2 := by
          simp only [hY]; ring
        rw [hsq]
        exact mul_le_mul_of_nonneg_right hgi (sq_nonneg _)
      rwa [MeasureTheory.integral_const_mul] at hle
    have hD2 : (0 : ℝ) ≤ D ^ 2 := sq_nonneg D
    calc ∫ ω, (Y i ω) ^ 2 ∂P
        ≤ D ^ 2 * ∫ ω, (LevyStochCalc.Brownian.Ito.polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
            (t i) (t (i + 1)) ω) ^ 2 ∂P := hstep
      _ ≤ D ^ 2 * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4)
            * (t (i + 1) - t i) ^ 2) := mul_le_mul_of_nonneg_left hζle hD2
      _ = D ^ 2 * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
            * (t (i + 1) - t i) ^ 2 := by ring
  calc ∑ i ∈ Finset.range N, ∫ ω, (Y i ω) ^ 2 ∂P
      ≤ ∑ i ∈ Finset.range N, D ^ 2
          * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (t (i + 1) - t i) ^ 2 := Finset.sum_le_sum hterm
    _ = D ^ 2 * (3 * ((2 * (6 + LevyStochCalc.Brownian.Ito.gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * ∑ i ∈ Finset.range N, (t (i + 1) - t i) ^ 2 := by rw [Finset.mul_sum]
