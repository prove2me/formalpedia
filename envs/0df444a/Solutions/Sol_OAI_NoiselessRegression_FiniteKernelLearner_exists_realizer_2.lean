-- Prove2me | solution 2 for OAI.NoiselessRegression.FiniteKernelLearner.exists_realizer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:31:02.452772+00:00
-- url     : https://prove2.me/submissions/b44f72c3-cdf6-4c15-bc9c-727e108a228e

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Realization.lean:L25-L40
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.FiniteKernelLearner.exists_realizer. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_Stopping
import Definitions.Def_OAI_Probability_ProjectionMoments_BorelRules
import Definitions.Def_OAI_Probability_ProjectionMoments_Kernels
import Definitions.Def_OAI_Probability_ProjectionMoments_Realization

-- ---- from OAI.Probability.ProjectionMoments.Realization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

lemma exists_realizer (K : FiniteKernelLearner d M T) (hK : K.BorelRules) : Nonempty K.Realizer := by
  classical
  let j₀ : State M := ⟨0,by simp⟩
  let : IsProbabilityMeasure (K.output 0 j₀) := K.output_probability 0 j₀
  let : Nonempty (UnitSphere d) := nonempty_of_isProbabilityMeasure (K.output 0 j₀)
  have ht (t : ℕ) (j : State M) : ∃ f : (Vector d × ℝ) → I → Bool × State M,
      Measurable (Function.uncurry f) ∧ ∀ obs, volume.map (f obs) = K.transition t j obs := by
    let κ : Kernel (Vector d × ℝ) (Bool × State M) := ⟨K.transition t j,hK.transition t j⟩
    let : IsMarkovKernel κ := ⟨K.transition_probability t j⟩
    exact κ.exists_measurable_map_eq_unitInterval
  have ho (t : ℕ) (j : State M) : ∃ g : I → UnitSphere d, Measurable g ∧ volume.map g = K.output t j := by
    let : IsProbabilityMeasure (K.output t j) := K.output_probability t j
    exact (K.output t j).exists_measurable_map_eq
  choose f hf hfl using ht
  choose g hg hgl using ho
  exact ⟨⟨f,hf,hfl,g,hg,hgl⟩⟩

end FiniteKernelLearner

namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

end FiniteKernelLearner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
open Learner


theorem solution : type_of% @_root_.OAI.NoiselessRegression.FiniteKernelLearner.exists_realizer := @_root_.OAI.NoiselessRegression.FiniteKernelLearner.exists_realizer
