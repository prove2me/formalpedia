-- Prove2me | solution 2 for OAI.ProjectionMoments.lowerDensity_is_density
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:13:43.574689+00:00
-- url     : https://prove2.me/submissions/f5394124-25d7-407d-af14-edbcd44ab570

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Graph.lean:L205-L224
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.lowerDensity_is_density. The node keeps its source
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
import Theorems.Thm_OAI_ProjectionMoments_ballAverage_eq

-- ---- from OAI.Probability.ProjectionMoments.Graph ----
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments

section GaussianGraph
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end GaussianGraph

section BallDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem lowerDensity_is_density (ν : Measure E) [IsFiniteMeasure ν] (m : ℕ)
    (A : Fin m → E) (hA : ν.map (rowMap A) ≪ (volume : Measure (Label m))) :
    volume.withDensity (fun y => lowerDensity ν m (A,y)) = ν.map (rowMap A) := by
  let ρ := ν.map (rowMap A)
  let v := IsUnifLocDoublingMeasure.vitaliFamily (volume : Measure (Label m)) 1
  have hneg : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun n => ?_)⟩
    · simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    · change (0 : ℝ) < ((n : ℝ) + 1)⁻¹
      positivity
  have hae : (fun y => lowerDensity ν m (A,y)) =ᵐ[volume] ρ.rnDeriv volume := by
    filter_upwards [v.ae_tendsto_rnDeriv_of_absolutelyContinuous hA] with y hy
    have ht := IsUnifLocDoublingMeasure.tendsto_closedBall_filterAt volume
      (K := (1 : ℝ)) (x := y) (fun _ : ℕ => y) (fun n => ((n : ℝ) + 1)⁻¹) hneg
      (Filter.Eventually.of_forall (fun n => Metric.mem_closedBall_self (by positivity)))
    have hlim := (hy.comp ht).liminf_eq
    simpa only [lowerDensity, ballAverage_eq, ρ, Function.comp_def] using hlim
  rw [withDensity_congr_ae hae]
  exact Measure.withDensity_rnDeriv_eq _ _ hA

end BallDensity

section Rescaling
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end Rescaling

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.lowerDensity_is_density := @_root_.OAI.ProjectionMoments.lowerDensity_is_density
