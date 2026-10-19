-- Prove2me | solution 2 for OAI.ProjectionMoments.rescaled_projection_ac
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:02:18.935495+00:00
-- url     : https://prove2.me/submissions/824037cd-be4f-43aa-ba49-38965c4d1ee1

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/CapTests.lean:L184-L202
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.rescaled_projection_ac. The node keeps its source
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

-- ---- from OAI.Probability.ProjectionMoments.CapTests ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
namespace ProjectionMoments
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma rescaled_projection_ac {ν : Measure E} {k : ℕ} (A : Fin k → E) (c : E) {r : ℝ} (hr : 0 < r)
    (hν : ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (ν.map (rescale c r)).map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  let T : (Fin k → ℝ) → (Fin k → ℝ) := fun y => r⁻¹ • (y-coordinateMap A c)
  have hT : Measurable T := by fun_prop
  have hv : (volume : Measure (Fin k → ℝ)).map T ≪ volume := by
    have he : T = (fun y : Fin k → ℝ => r⁻¹ • y) ∘ (fun y => y + -coordinateMap A c) := by
      funext y; simp [T,sub_eq_add_neg]
    rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
      Measure.IsAddRightInvariant.map_add_right_eq_self, Measure.map_addHaar_smul volume (inv_ne_zero hr.ne')]
    exact Measure.smul_absolutelyContinuous
  have hh := (hν.map hT).trans hv
  rw [Measure.map_map hT (by fun_prop)] at hh
  rw [Measure.map_map (by fun_prop) (measurable_rescale c r)]
  convert hh using 1
  congr 1
  funext s
  ext i
  simp [T, rescale, coordinateMap_apply, real_inner_smul_left, inner_sub_left]

end ProjectionMoments

end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.rescaled_projection_ac := @_root_.OAI.ProjectionMoments.rescaled_projection_ac
