-- Prove2me | solution 1 for OAI.NoiselessRegression.FiniteKernelLearner.exists_realizer
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:50:20.179602+00:00
-- url     : https://prove2.me/submissions/6e8e9747-e257-47a2-ac18-1ddfefca4b70

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

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
open Learner
variable {d M T : ℕ}


theorem solution (K : FiniteKernelLearner d M T) (hK : K.BorelRules) : Nonempty K.Realizer := by
  have hne : Nonempty (UnitSphere d) := by
    have := K.output_probability 0 0
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := K.output 0 0)
    rw [Set.univ_eq_empty_iff.mpr h, measure_empty] at h1
    exact zero_ne_one h1
  have hT : ∀ t j, ∃ f : (Vector d × ℝ) → I → Bool × State M,
      Measurable (Function.uncurry f) ∧ ∀ obs, volume.map (f obs) = K.transition t j obs := by
    intro t j
    let κ : Kernel (Vector d × ℝ) (Bool × State M) := ⟨K.transition t j, hK.transition t j⟩
    have : IsMarkovKernel κ := ⟨fun obs => K.transition_probability t j obs⟩
    exact κ.exists_measurable_map_eq_unitInterval
  have hO : ∀ t j, ∃ f : I → UnitSphere d, Measurable f ∧ volume.map f = K.output t j := by
    intro t j
    have := K.output_probability t j
    exact (K.output t j).exists_measurable_map_eq
  choose f hf1 hf2 using hT
  choose g hg1 hg2 using hO
  exact ⟨⟨f, hf1, hf2, g, hg1, hg2⟩⟩

