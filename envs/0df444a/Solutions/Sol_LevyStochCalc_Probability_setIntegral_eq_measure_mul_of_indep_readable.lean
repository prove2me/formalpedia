-- Prove2me | solution 1 for LevyStochCalc.Probability.setIntegral_eq_measure_mul_of_indep_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:25:30.991456+00:00
-- url     : https://prove2.me/submissions/c59a5999-0bc0-4b86-b0ca-b3657eaf3635

import Definitions.Def_KLSModular_LevyStochCalc_Probability_IndepLimit

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Probability/IndepLimit.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction
variable {Ω 𝓧 : Type*} {m mΩ : MeasurableSpace Ω} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  [TopologicalSpace 𝓧] [MeasurableSpace 𝓧] [BorelSpace 𝓧] [HasOuterApproxClosed 𝓧]
omit [HasOuterApproxClosed 𝓧] in
/-- For `A ∈ m` and `X` independent of `m`, `∫_A f ∘ X = P(A) ∫ f ∘ X`. -/
lemma solution (hm : m ≤ mΩ) {X : Ω → 𝓧}
    (hX : Measurable[mΩ] X) (hind : Indep m (MeasurableSpace.comap X inferInstance) P)
    {A : Set Ω} (hA : MeasurableSet[m] A) (f : 𝓧 →ᵇ ℝ) :
    ∫ ω in A, f (X ω) ∂P = (P A).toReal * ∫ ω, f (X ω) ∂P := by
  have hA' : MeasurableSet[mΩ] A := hm _ hA
  have hindf : IndepFun (A.indicator (1 : Ω → ℝ)) (fun ω => f (X ω)) P := by
    change Indep (MeasurableSpace.comap _ _) (MeasurableSpace.comap _ _) P
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left hind ?_) ?_
    · have hmeas : Measurable[m] (A.indicator (1 : Ω → ℝ)) := by
        letI := m
        exact measurable_const.indicator hA
      exact hmeas.comap_le
    · rw [show (fun ω => f (X ω)) = f ∘ X from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (f.continuous.measurable.comap_le)
  have hfX : Integrable (fun ω => f (X ω)) P :=
    Integrable.of_bound (f.continuous.measurable.comp hX).aestronglyMeasurable ‖f‖
      (ae_of_all _ fun ω => f.norm_coe_le_norm _)
  have h := hindf.integral_mul_eq_mul_integral
    ((integrable_const (1 : ℝ)).indicator hA').aestronglyMeasurable hfX.aestronglyMeasurable
  have hfun : (A.indicator (1 : Ω → ℝ) * fun ω => f (X ω)) = A.indicator (fun ω => f (X ω)) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [hω]
  rw [integral_indicator_one hA', hfun, integral_indicator hA', measureReal_def] at h
  exact h
