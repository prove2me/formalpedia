-- Prove2me | solution 1 for MeasureTheory.fubini_swap_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:48:53.521096+00:00
-- url     : https://prove2.me/submissions/586e54c3-df72-4839-97cb-5b12dc3320a6

import Definitions.Def_KLS408915f_MathFin_Foundations_DoobLpMaximalInequality
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Probability.Martingale.OptionalStopping
import Theorems.Thm_MeasureTheory_inner_t_integral_408915f

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
private lemma MeasureTheory.runMax_measurable {f : ℕ → Ω → ℝ} {𝒢 : Filtration ℕ m0}
    (hsub : Submartingale f 𝒢 μ) (n : ℕ) :
    Measurable (MeasureTheory.runMax f n) := by
  unfold MeasureTheory.runMax
  exact Finset.measurable_range_sup''
    (fun k _ ↦ ((hsub.stronglyMeasurable k).mono (𝒢.le k)).measurable)
namespace MeasureTheory
end MeasureTheory
open MeasureTheory in
/-- Fubini swap stage (Tier A.2 Stage 1).

    For `p > 1`, a non-negative submartingale `f`, and a time `n`, the
    iterated integral
       `∫⁻ t in Ioi 0, ofReal(t^(p-2)) ⋅ ∫⁻_{fstar ≥ t} ofReal(f_n) dμ`
    equals
       `∫⁻ ω, ofReal(f_n ω) ⋅ ofReal((fstar ω)^(p-1) / (p-1)) dμ`.

    Proof: rewrite the inner set-integral as an indicator-weighted full
    integral; apply `MeasureTheory.lintegral_lintegral_swap` to swap the
    order of integration; then evaluate the inner `t`-integral pointwise
    via `inner_t_integral`. -/
 lemma solution
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) :
    ∫⁻ t in Set.Ioi (0:ℝ),
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1) / (p - 1)) ∂μ := by
  -- Measurability of runMax f n and f n.
  have hRunMaxMeas : Measurable (MeasureTheory.runMax f n) := runMax_measurable hsub n
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  -- Joint set {(t,ω) | t ≤ runMax f n ω} is product-measurable as the
  -- preimage of {(a,b) : ℝ×ℝ | a ≤ b} under (fst, runMax ∘ snd).
  have hJointSet : MeasurableSet {pr : ℝ × Ω | pr.1 ≤ MeasureTheory.runMax f n pr.2} := by
    have h1 : Measurable (fun pr : ℝ × Ω ↦ pr.1) := measurable_fst
    have h2 : Measurable (fun pr : ℝ × Ω ↦ MeasureTheory.runMax f n pr.2) :=
      hRunMaxMeas.comp measurable_snd
    exact measurableSet_le h1 h2
  -- Step 1: rewrite the inner setLIntegral as a full lintegral via indicator.
  have step1 : ∀ t,
      ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
        = ∫⁻ ω, {ω | t ≤ MeasureTheory.runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    rw [lintegral_indicator (measurableSet_le measurable_const hRunMaxMeas)]
  -- Step 2: pull the constant `ofReal(t^(p-2))` inside the inner lintegral.
  have step2 : ∀ t, ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ ω, {ω | t ≤ MeasureTheory.runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ
      = ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
              {ω | t ≤ MeasureTheory.runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hsubM).indicator
            (measurableSet_le measurable_const hRunMaxMeas))).symm
  simp_rw [step1, step2]
  -- Joint measurability of the bivariate integrand.
  have hF_meas : Measurable (fun pr : ℝ × Ω ↦
      ENNReal.ofReal (pr.1 ^ (p - 2)) *
        {q : ℝ × Ω | q.1 ≤ MeasureTheory.runMax f n q.2}.indicator
          (fun q ↦ ENNReal.ofReal (f n q.2)) pr) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_fst : Measurable (fun pr : ℝ × Ω ↦ pr.1)).pow_const (p - 2)
    · refine Measurable.indicator ?_ hJointSet
      exact ENNReal.measurable_ofReal.comp (hsubM.comp measurable_snd)
  -- Rewrite the LHS with indicator on Ioi 0 (so it becomes a full lintegral
  -- over ℝ) and apply lintegral_lintegral_swap on ℝ × Ω.
  rw [← lintegral_indicator measurableSet_Ioi]
  -- LHS now is ∫⁻ t, (Ioi 0).indicator (fun t ↦ ∫⁻ ω, F(t,ω) ∂μ) t ∂volume
  -- Massage to ∫⁻ t, ∫⁻ ω, (Ioi 0).indicator (fun _ ↦ F(t,ω)) t ∂μ
  have lhs_rewrite : ∫⁻ a, (Set.Ioi (0:ℝ)).indicator
        (fun t ↦ ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
                {ω | t ≤ MeasureTheory.runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ) a
      = ∫⁻ t, ∫⁻ ω, (Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {ω | s ≤ MeasureTheory.runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ioi (0:ℝ)
    · rw [Set.indicator_of_mem ht]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ← lintegral_zero (μ := μ)]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_notMem ht]
  rw [lhs_rewrite]
  -- Now apply lintegral_lintegral_swap.
  have hSwap_meas : AEMeasurable
      (Function.uncurry (fun t ω ↦ (Set.Ioi (0:ℝ)).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω | s ≤ MeasureTheory.runMax f n ω}.indicator
              (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t))
      (volume.prod μ) := by
    refine (Measurable.indicator ?_ ?_).aemeasurable
    · exact hF_meas
    · exact measurable_fst measurableSet_Ioi
  rw [lintegral_lintegral_swap hSwap_meas]
  -- Now have ∫⁻ ω, ∫⁻ t, indicator(Ioi 0) F(t,ω) ∂volume ∂μ.
  -- For each ω, the inner is the integral over Ioi 0 of
  --   ofReal(t^(p-2)) * 𝟙{t ≤ runMax f n ω} * ofReal(f n ω)
  -- = ofReal(f n ω) * (∫⁻ t in Ioi 0, ofReal(t^(p-2)) * 𝟙{t ≤ fstar ω})
  -- = ofReal(f n ω) * ofReal((runMax f n ω)^(p-1) / (p-1))  [inner_t_integral]
  apply lintegral_congr_ae
  filter_upwards with ω
  -- Reduce the inner integral.
  have h_inner_simp :
      ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω' | s ≤ MeasureTheory.runMax f n ω'}.indicator
              (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
        = ENNReal.ofReal (f n ω) *
            ENNReal.ofReal ((MeasureTheory.runMax f n ω) ^ (p - 1) / (p - 1)) := by
    -- Rewrite the inner indicator
    have h_pointwise : ∀ t,
        (Set.Ioi (0:ℝ)).indicator
            (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
              {ω' | s ≤ MeasureTheory.runMax f n ω'}.indicator
                (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
          = ENNReal.ofReal (f n ω) *
              ((Set.Ioi (0:ℝ)).indicator
                (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                  {s : ℝ | s ≤ MeasureTheory.runMax f n ω}.indicator
                    (fun _ ↦ (1 : ℝ≥0∞)) s)) t := by
      intro t
      by_cases ht : t ∈ Set.Ioi (0:ℝ)
      · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        by_cases hle : t ≤ MeasureTheory.runMax f n ω
        · have hmem1 : ω ∈ {ω' | t ≤ MeasureTheory.runMax f n ω'} := hle
          have hmem2 : t ∈ {s : ℝ | s ≤ MeasureTheory.runMax f n ω} := hle
          rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, mul_one]
          ring
        · have hnmem1 : ω ∉ {ω' | t ≤ MeasureTheory.runMax f n ω'} := hle
          have hnmem2 : t ∉ {s : ℝ | s ≤ MeasureTheory.runMax f n ω} := hle
          rw [Set.indicator_of_notMem hnmem1, Set.indicator_of_notMem hnmem2,
              mul_zero, mul_zero]
      · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, mul_zero]
    simp_rw [h_pointwise]
    rw [lintegral_const_mul']
    · -- The inner lintegral matches inner_t_integral.
      have h_eq :
          ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {s : ℝ | s ≤ MeasureTheory.runMax f n ω}.indicator
                  (fun _ ↦ (1 : ℝ≥0∞)) s) t
            = ∫⁻ t in Set.Ioi (0:ℝ),
                ENNReal.ofReal (t ^ (p - 2)) *
                  {s : ℝ | s ≤ MeasureTheory.runMax f n ω}.indicator
                    (fun _ ↦ (1 : ℝ≥0∞)) t := by
        rw [← lintegral_indicator measurableSet_Ioi]
      rw [h_eq, MeasureTheory.inner_t_integral_408915f (runMax_nonneg hnonneg n ω) hp]
    · exact ENNReal.ofReal_ne_top
  rw [h_inner_simp]
