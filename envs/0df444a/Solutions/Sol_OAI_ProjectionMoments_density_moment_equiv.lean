-- Prove2me | solution 1 for OAI.ProjectionMoments.density_moment_equiv
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:26:42.67105+00:00
-- url     : https://prove2.me/submissions/40be3e1b-9871-447b-b162-0d0fc77a772f

import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
theorem solution {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (e : X ≃ᵐ X) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (he : μ.map e = c • μ) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : (μ.withDensity f).map e = μ.withDensity g) (n : ℕ) :
    ∫⁻ y, g y ^ (n+1) ∂μ = c^n * ∫⁻ x, f x ^ (n+1) ∂μ := by
  have hset : ∀ s, MeasurableSet s → μ s < ∞ →
      ∫⁻ x in s, g (e x) ∂μ = ∫⁻ x in s, c * f x ∂μ := by
    intro s hs _
    have hs' : MeasurableSet (e.symm ⁻¹' s) := e.symm.measurable hs
    have h1 : ∫⁻ x in s, g (e x) ∂μ = c * μ.withDensity g (e.symm ⁻¹' s) := by
      rw [← lintegral_indicator hs]
      have : s.indicator (fun x => g (e x)) = fun x => ((e.symm ⁻¹' s).indicator g) (e x) := by
        funext x
        by_cases hx : x ∈ s
        · have h' : e x ∈ e.symm ⁻¹' s := by
            show e.symm (e x) ∈ s; rw [MeasurableEquiv.symm_apply_apply]; exact hx
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem h']
        · have h' : e x ∉ e.symm ⁻¹' s := by
            show ¬ e.symm (e x) ∈ s; rw [MeasurableEquiv.symm_apply_apply]; exact hx
          rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem h']
      rw [this, ← lintegral_map_equiv, he, lintegral_smul_measure, lintegral_indicator hs',
        withDensity_apply _ hs', smul_eq_mul]
    have h2 : ∫⁻ x in s, c * f x ∂μ = c * μ.withDensity g (e.symm ⁻¹' s) := by
      rw [lintegral_const_mul _ hf, ← withDensity_apply _ hs, ← hfg, Measure.map_apply e.measurable hs']
      congr 2; ext x; simp
    rw [h1, h2]
  have key := ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (hg.comp e.measurable) (hf.const_mul c) hset
  have h3 : c * ∫⁻ y, g y ^ (n+1) ∂μ = c * (c ^ n * ∫⁻ x, f x ^ (n+1) ∂μ) := by
    have h4 : ∫⁻ y, g y ^ (n+1) ∂(c • μ) = c * ∫⁻ y, g y ^ (n+1) ∂μ := by
      rw [lintegral_smul_measure, smul_eq_mul]
    rw [← h4, ← he, lintegral_map_equiv, ← mul_assoc, ← pow_succ',
      ← lintegral_const_mul _ (hf.pow_const _)]
    apply lintegral_congr_ae
    filter_upwards [key] with x hx
    simp only [Function.comp_apply] at hx
    rw [hx, mul_pow]
  exact (ENNReal.mul_right_inj hc0 hct).1 h3

