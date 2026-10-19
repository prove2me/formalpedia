-- Prove2me | solution 2 for OAI.ProjectionMoments.capReference_sum_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:16:34.306587+00:00
-- url     : https://prove2.me/submissions/ecb2f609-9d04-4412-9de1-3ac3481e5154

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/CapDomination.lean:L72-L89
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.capReference_sum_le_one. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_CapTests
import Definitions.Def_OAI_Probability_ProjectionMoments_CapDuality
import Definitions.Def_OAI_Probability_ProjectionMoments_WeightedCover

-- ---- from OAI.Probability.ProjectionMoments.CapDomination ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments

lemma capReference_sum_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {k : ℕ} {J : Type*} [Fintype J]
    (K : J → (Fin k → E) × Label k → ℝ≥0∞) (hK : ∀ j, Measurable (K j))
    (hKsum : ∀ z, ∑ j, K j z ≤ 1) (c : E) (r : ℝ) : ∑ j, capReference (K j) c r ≤ 1 := by
  classical
  simp only [capReference]
  rw [← lintegral_finsetSum _ (fun j _ => by fun_prop)]
  calc
    _ = ∫⁻ X, ∫⁻ z, ∑ j, K j (X,capReferenceLabel c r X z) ∂unitBallLaw k
        ∂Measure.pi (fun _ => stdGaussian E) := by
      apply lintegral_congr
      intro X
      exact (lintegral_finsetSum _ (fun j _ => by fun_prop)).symm
    _ ≤ ∫⁻ X, ∫⁻ z : Label k, (1 : ℝ≥0∞) ∂unitBallLaw k
        ∂Measure.pi (fun _ : Fin k => stdGaussian E) :=
      lintegral_mono (fun X => lintegral_mono (fun z => hKsum _))
    _ = 1 := by simp

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.capReference_sum_le_one := @_root_.OAI.ProjectionMoments.capReference_sum_le_one
