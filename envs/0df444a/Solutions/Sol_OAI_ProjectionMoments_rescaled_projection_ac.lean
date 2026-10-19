-- Prove2me | solution 1 for OAI.ProjectionMoments.rescaled_projection_ac
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:48:52.938771+00:00
-- url     : https://prove2.me/submissions/21748f60-ee95-4368-b1cc-6b1eb919939a

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

open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
theorem solution {ν : Measure E} {k : ℕ} (A : Fin k → E) (c : E) {r : ℝ} (hr : 0 < r)
    (hν : ν.map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ))) :
    (ν.map (rescale c r)).map (coordinateMap A) ≪ (volume : Measure (Fin k → ℝ)) := by
  set C := coordinateMap A
  have hC : Measurable C := (LinearMap.continuous_of_finiteDimensional C).measurable
  have hR : Measurable (rescale c r) := by unfold rescale; fun_prop
  set b : Fin k → ℝ := -(r⁻¹ • C c)
  let T : (Fin k → ℝ) → (Fin k → ℝ) := fun y => r⁻¹ • y + b
  have hT : Measurable T := by fun_prop
  have hCR : C ∘ rescale c r = T ∘ C := by
    funext x
    simp only [Function.comp_apply, rescale, T, b, map_smul, map_sub]
    rw [smul_sub]; abel
  rw [Measure.map_map hC hR, hCR, ← Measure.map_map hT hC]
  refine (hν.map hT).trans ?_
  have h1 : Measurable (fun y : Fin k → ℝ => r⁻¹ • y) := by fun_prop
  have h2 : Measurable (fun y : Fin k → ℝ => y + b) := by fun_prop
  have hTc : T = (fun y => y + b) ∘ (fun y : Fin k → ℝ => r⁻¹ • y) := rfl
  rw [hTc, ← Measure.map_map h2 h1, Measure.map_addHaar_smul _ (inv_ne_zero hr.ne'),
    Measure.map_smul, map_add_right_eq_self]
  exact Measure.smul_absolutelyContinuous

