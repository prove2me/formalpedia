-- Prove2me | solution 2 for OAI.ProjectionMoments.density_moment_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:21:13.251211+00:00
-- url     : https://prove2.me/submissions/77ce2516-b8ec-4775-9184-75a77ab33d1f

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/GaussianDensity.lean:L148-L176
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.density_moment_equiv. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Probability.ProjectionMoments.GaussianDensity ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

lemma map_withDensity_equiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (e : X ≃ᵐ Y) (f : X → ℝ≥0∞) (hf : Measurable f) :
    (μ.withDensity f).map e = (μ.map e).withDensity (fun y => f (e.symm y)) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs, ← lintegral_indicator hs,
    lintegral_map (show Measurable (s.indicator (fun y => f (e.symm y))) from
      (hf.comp e.symm.measurable).indicator hs) e.measurable]
  have he (x : X) : s.indicator (fun y => f (e.symm y)) (e x) =
      (e ⁻¹' s).indicator f x := by
    by_cases hx : e x ∈ s <;> simp [hx]
  simp_rw [he]
  exact (lintegral_indicator (hs.preimage e.measurable) f).symm

lemma density_moment_equiv {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ]
    (e : X ≃ᵐ X) (c : ℝ≥0∞) (hc0 : c ≠ 0) (hct : c ≠ ∞)
    (he : μ.map e = c • μ) {f g : X → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g)
    (hfg : (μ.withDensity f).map e = μ.withDensity g) (n : ℕ) :
    ∫⁻ y, g y ^ (n+1) ∂μ = c^n * ∫⁻ x, f x ^ (n+1) ∂μ := by
  have hd : g =ᵐ[μ] (fun y => c * f (e.symm y)) := by
    apply (withDensity_eq_iff_of_sigmaFinite hg.aemeasurable (by fun_prop)).mp
    rw [← hfg, map_withDensity_equiv μ e f hf, he, withDensity_smul_measure]
    exact (withDensity_smul c (hf.comp e.symm.measurable)).symm
  have hd' : (fun y => g y ^ (n+1)) =ᵐ[μ]
      (fun y => (c * f (e.symm y)) ^ (n+1)) := by
    filter_upwards [hd] with y hy
    rw [hy]
  rw [lintegral_congr_ae hd']
  simp_rw [mul_pow]
  rw [lintegral_const_mul _ (by fun_prop)]
  have hchange : c * (∫⁻ y, f (e.symm y) ^ (n+1) ∂μ) = ∫⁻ x, f x ^ (n+1) ∂μ := by
    calc
      _ = ∫⁻ y, f (e.symm y) ^ (n+1) ∂(c • μ) := by
        simp only [lintegral_smul_measure, smul_eq_mul]
      _ = _ := by
        rw [← he, lintegral_map_equiv]
        simp
  have hchange' : (∫⁻ y, f (e.symm y) ^ (n+1) ∂μ) =
      c⁻¹ * ∫⁻ x, f x ^ (n+1) ∂μ := by
    rw [← hchange, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [hchange', pow_succ, mul_assoc, ← mul_assoc c, ENNReal.mul_inv_cancel hc0 hct,
    one_mul]

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.density_moment_equiv := @_root_.OAI.ProjectionMoments.density_moment_equiv
