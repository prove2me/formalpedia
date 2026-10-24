-- Prove2me | solution 1 for MeasureTheory.fubini_swap_truncated_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T16:48:54.826708+00:00
-- url     : https://prove2.me/submissions/0737b9a9-fa07-40c6-bdbc-cc5618180ec7

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
/-- Truncated inner t-integral: for `fstar ≥ 0` and `K > 0`,
       `∫⁻ t in Ioi 0, t^(p-2) ⋅ 𝟙{0 < t ≤ K ∧ t ≤ fstar}
         = ofReal(min fstar K^(p-1) / (p-1))`.
    Identical to `inner_t_integral` but with an extra `t ≤ K` constraint,
    which makes the inner Ioc become `Ioc 0 (min fstar K)`. -/
private lemma MeasureTheory.inner_t_integral_truncated
    {fstar K p : ℝ} (hfstar : 0 ≤ fstar) (hK : 0 < K) (hp : 1 < p) :
    ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
        ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
         {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t)
      = ENNReal.ofReal ((min fstar K) ^ (p - 1) / (p - 1)) := by
  -- Reduce to the untruncated case via `t ≤ K ∧ t ≤ fstar ↔ t ≤ min fstar K`.
  have h_eq : ∀ t,
      (Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
        {t : ℝ | t ≤ fstar}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t
      = {t : ℝ | t ≤ min fstar K}.indicator (fun _ ↦ (1 : ℝ≥0∞)) t := fun t ↦ by
    by_cases hK' : t ≤ K
    · by_cases hfs : t ≤ fstar
      · rw [Set.indicator_of_mem (show t ∈ Set.Iic K from hK'),
            Set.indicator_of_mem (show t ∈ {t : ℝ | t ≤ fstar} from hfs),
            Set.indicator_of_mem (show t ∈ {t : ℝ | t ≤ min fstar K} from le_min hfs hK'),
            mul_one]
      · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | t ≤ fstar} from hfs),
            Set.indicator_of_notMem
              (show t ∉ {t : ℝ | t ≤ min fstar K} from
                fun h ↦ hfs (h.trans (min_le_left _ _))),
            mul_zero]
    · rw [Set.indicator_of_notMem (show t ∉ Set.Iic K from hK'),
          Set.indicator_of_notMem
            (show t ∉ {t : ℝ | t ≤ min fstar K} from
              fun h ↦ hK' (h.trans (min_le_right _ _))),
          zero_mul]
  simp_rw [h_eq]
  exact inner_t_integral_408915f (le_min hfstar hK.le) hp
namespace MeasureTheory
end MeasureTheory
open MeasureTheory in
/-- Truncated Fubini swap. Analog of `fubini_swap` but with the outer
    `t`-integral restricted to `Ioc 0 K`, producing
    `min (runMax f n) K` in the post-swap formula. -/
 lemma solution
    [IsFiniteMeasure μ] {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {p : ℝ}
    (hsub : Submartingale f 𝒢 μ) (hnonneg : ∀ n ω, 0 ≤ f n ω)
    (hp : 1 < p) (n : ℕ) (K : ℝ) (hK : 0 < K) :
    ∫⁻ t in Set.Ioc (0:ℝ) K,
        ENNReal.ofReal (t ^ (p - 2)) *
          ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
      = ∫⁻ ω, ENNReal.ofReal (f n ω) *
              ENNReal.ofReal ((min (MeasureTheory.runMax f n ω) K) ^ (p - 1) / (p - 1)) ∂μ := by
  -- Rewrite the LHS via an Ioi 0 outer integral with an Iic K indicator,
  -- so we can reuse the bivariate Fubini machinery.
  have hRunMaxMeas : Measurable (MeasureTheory.runMax f n) := runMax_measurable hsub n
  have hsubM : Measurable (f n) :=
    ((hsub.stronglyMeasurable n).measurable).mono (𝒢.le n) le_rfl
  have hIocEqRestrict : Set.Ioc (0:ℝ) K = Set.Ioi 0 ∩ Set.Iic K := by
    ext t
    simp [Set.mem_Ioc, Set.mem_Ioi, Set.mem_Iic, and_comm]
  rw [hIocEqRestrict]
  rw [← MeasureTheory.lintegral_indicator (measurableSet_Ioi.inter measurableSet_Iic)]
  -- Step 1: rewrite the inner setLIntegral as a full lintegral via indicator.
  have step1 : ∀ t,
      ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ
        = ∫⁻ ω, {ω | t ≤ MeasureTheory.runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    rw [lintegral_indicator (measurableSet_le measurable_const hRunMaxMeas)]
  -- Step 2: pull the constant ofReal(t^(p-2)) inside the inner lintegral.
  have step2 : ∀ t, ENNReal.ofReal (t ^ (p - 2)) *
        ∫⁻ ω, {ω | t ≤ MeasureTheory.runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ
      = ∫⁻ ω, ENNReal.ofReal (t ^ (p - 2)) *
              {ω | t ≤ MeasureTheory.runMax f n ω}.indicator
                (fun ω ↦ ENNReal.ofReal (f n ω)) ω ∂μ := by
    intro t
    exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hsubM).indicator
            (measurableSet_le measurable_const hRunMaxMeas))).symm
  -- Joint measurability of the bivariate integrand (Ioi 0 ∩ Iic K is product-measurable).
  have hJointSet : MeasurableSet {pr : ℝ × Ω | pr.1 ≤ MeasureTheory.runMax f n pr.2} := by
    have h1 : Measurable (fun pr : ℝ × Ω ↦ pr.1) := measurable_fst
    have h2 : Measurable (fun pr : ℝ × Ω ↦ MeasureTheory.runMax f n pr.2) :=
      hRunMaxMeas.comp measurable_snd
    exact measurableSet_le h1 h2
  have hF_meas : Measurable (fun pr : ℝ × Ω ↦
      ENNReal.ofReal (pr.1 ^ (p - 2)) *
        {q : ℝ × Ω | q.1 ≤ MeasureTheory.runMax f n q.2}.indicator
          (fun q ↦ ENNReal.ofReal (f n q.2)) pr) := by
    refine Measurable.mul ?_ ?_
    · refine ENNReal.measurable_ofReal.comp ?_
      exact (measurable_fst : Measurable (fun pr : ℝ × Ω ↦ pr.1)).pow_const (p - 2)
    · refine Measurable.indicator ?_ hJointSet
      exact ENNReal.measurable_ofReal.comp (hsubM.comp measurable_snd)
  -- Rewrite outer indicator + push into bivariate integrand.
  have h_outer_eq : ∫⁻ a, (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
        (fun t ↦ ENNReal.ofReal (t ^ (p - 2)) *
                ∫⁻ ω in {ω | t ≤ MeasureTheory.runMax f n ω}, ENNReal.ofReal (f n ω) ∂μ) a
      = ∫⁻ t, ∫⁻ ω, (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                {ω | s ≤ MeasureTheory.runMax f n ω}.indicator
                  (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t ∂μ := by
    apply lintegral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ Set.Ioi (0:ℝ) ∩ Set.Iic K
    · rw [Set.indicator_of_mem ht, step1, step2]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem ht, ← lintegral_zero (μ := μ)]
      apply lintegral_congr_ae
      filter_upwards with ω
      rw [Set.indicator_of_notMem ht]
  rw [h_outer_eq]
  -- Apply Fubini.
  have hSwap_meas : AEMeasurable
      (Function.uncurry (fun t ω ↦ (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω | s ≤ MeasureTheory.runMax f n ω}.indicator
              (fun ω ↦ ENNReal.ofReal (f n ω)) ω) t))
      (volume.prod μ) := by
    refine (Measurable.indicator ?_ ?_).aemeasurable
    · exact hF_meas
    · exact measurable_fst (measurableSet_Ioi.inter measurableSet_Iic)
  rw [lintegral_lintegral_swap hSwap_meas]
  apply lintegral_congr_ae
  filter_upwards with ω
  -- Pointwise: rewrite indicator product, pull out ofReal(f_n ω), use inner_t_integral_truncated.
  have h_pointwise : ∀ t,
      (Set.Ioi (0:ℝ) ∩ Set.Iic K).indicator
          (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
            {ω' | s ≤ MeasureTheory.runMax f n ω'}.indicator
              (fun ω' ↦ ENNReal.ofReal (f n ω')) ω) t
        = ENNReal.ofReal (f n ω) *
            ((Set.Ioi (0:ℝ)).indicator
              (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
                ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) s *
                 {s : ℝ | s ≤ MeasureTheory.runMax f n ω}.indicator
                  (fun _ ↦ (1 : ℝ≥0∞)) s)) t) := by
    intro t
    by_cases ht_pos : t ∈ Set.Ioi (0:ℝ)
    · by_cases ht_K : t ∈ Set.Iic K
      · have ht_both : t ∈ Set.Ioi (0:ℝ) ∩ Set.Iic K := ⟨ht_pos, ht_K⟩
        rw [Set.indicator_of_mem ht_both, Set.indicator_of_mem ht_pos,
            Set.indicator_of_mem ht_K, one_mul]
        by_cases h_le : t ≤ MeasureTheory.runMax f n ω
        · have hmem1 : ω ∈ {ω' | t ≤ MeasureTheory.runMax f n ω'} := h_le
          have hmem2 : t ∈ {s : ℝ | s ≤ MeasureTheory.runMax f n ω} := h_le
          rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2, mul_one]
          ring
        · have hnmem1 : ω ∉ {ω' | t ≤ MeasureTheory.runMax f n ω'} := h_le
          have hnmem2 : t ∉ {s : ℝ | s ≤ MeasureTheory.runMax f n ω} := h_le
          rw [Set.indicator_of_notMem hnmem1, Set.indicator_of_notMem hnmem2]
          ring
      · have ht_not_both : t ∉ Set.Ioi (0:ℝ) ∩ Set.Iic K := fun h ↦ ht_K h.2
        rw [Set.indicator_of_notMem ht_not_both, Set.indicator_of_mem ht_pos,
            Set.indicator_of_notMem ht_K, zero_mul, mul_zero, mul_zero]
    · have ht_not_both : t ∉ Set.Ioi (0:ℝ) ∩ Set.Iic K := fun h ↦ ht_pos h.1
      rw [Set.indicator_of_notMem ht_not_both,
          Set.indicator_of_notMem ht_pos, mul_zero]
  simp_rw [h_pointwise]
  rw [lintegral_const_mul']
  · -- Convert to setLIntegral on Ioi 0, then apply inner_t_integral_truncated.
    have h_unfold :
        ∫⁻ t, (Set.Ioi (0:ℝ)).indicator
            (fun s ↦ ENNReal.ofReal (s ^ (p - 2)) *
              ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) s *
               {s : ℝ | s ≤ MeasureTheory.runMax f n ω}.indicator
                (fun _ ↦ (1 : ℝ≥0∞)) s)) t
          = ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t ^ (p - 2)) *
              ((Set.Iic K).indicator (fun _ ↦ (1 : ℝ≥0∞)) t *
               {t : ℝ | t ≤ MeasureTheory.runMax f n ω}.indicator
                (fun _ ↦ (1 : ℝ≥0∞)) t) := by
      rw [← lintegral_indicator measurableSet_Ioi]
    rw [h_unfold]
    rw [inner_t_integral_truncated (runMax_nonneg hnonneg n ω) hK hp]
  · exact ENNReal.ofReal_ne_top
