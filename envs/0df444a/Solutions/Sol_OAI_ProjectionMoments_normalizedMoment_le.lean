-- Prove2me | solution 1 for OAI.ProjectionMoments.normalizedMoment_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:46:44.240429+00:00
-- url     : https://prove2.me/submissions/a6f6ff68-1d17-4cdd-8e72-18aefd5c0858

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/BallMoments.lean:L89-L108
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.normalizedMoment_le. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames
import Definitions.Def_OAI_Probability_ProjectionMoments_SphereDensity
import Definitions.Def_OAI_Probability_ProjectionMoments_FrameMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_RieszPotential
import Definitions.Def_OAI_Probability_ProjectionMoments_Polar
import Definitions.Def_OAI_Probability_ProjectionMoments_BallMoments
import Theorems.Thm_OAI_ProjectionMoments_lintegral_polarRows_eq_frame

-- ---- from OAI.Probability.ProjectionMoments.BallMoments ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

section
attribute [fun_prop] measurable_polarRows
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma normalizedMoment_le (ν : Measure E) [IsFiniteMeasure ν] {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) {u : Fin k → E} (hu : Orthonormal ℝ u) (n : ℕ) :
    (∫⁻ X, ∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k
      ∂Measure.pi (fun _ => stdGaussian E)) ≤
      unitBallVolume k ^ n * ∫⁻ A, labelMoment ν k n A ∂frameLaw u := by
  have hpoint (X : Fin k → E) :
      (∫⁻ y, normalizedDensity ν k u (X,y)^(n+1) ∂unitBallLaw k) ≤
        unitBallVolume k ^ n * labelMoment ν k n (polarRows u X) := by
    simp only [unitBallLaw, normalizedDensity, mul_pow, lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_const_mul _ (by fun_prop), ← mul_assoc,
      pow_succ', ← mul_assoc, ENNReal.inv_mul_cancel (unitBallVolume_ne_zero k) (unitBallVolume_ne_top k), one_mul]
    apply mul_le_mul' le_rfl
    have he : labelMoment ν k n (polarRows u X) =
        ∫⁻ y : Label k, lowerDensity ν k (polarRows u X,y)^(n+1) :=
      (PiLp.volume_preserving_toLp (Fin k)).lintegral_comp
        (show Measurable (fun y : Label k => lowerDensity ν k (polarRows u X,y)^(n+1)) by fun_prop)
    rw [he]
    exact setLIntegral_le_lintegral _ _
  apply (lintegral_mono hpoint).trans
  rw [lintegral_const_mul _ (by fun_prop), lintegral_polarRows_eq_frame hk hu _ (by fun_prop)]

end

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.normalizedMoment_le := @_root_.OAI.ProjectionMoments.normalizedMoment_le
