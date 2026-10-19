-- Prove2me | solution 1 for OAI.NoiselessRegression.Learner.continuation_tagged_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:41:44.713868+00:00
-- url     : https://prove2.me/submissions/acbfd09f-83e2-4128-83da-3e86fa41b1f3

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
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel

open OAI OAI.NoiselessRegression OAI.NoiselessRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
variable {d M T : ℕ}


theorem solution {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    {w : ℕ → State M → Vector d → ℝ≥0∞}
    (n k : ℕ) (hnk : n+k ≤ T) (j : TaggedState M T) (s : Vector d) :
    continuation (taggedStep τ) (taggedWeight w) n k j s =
      match j with
      | .inl a => stoppedContinuation τ w n k a s
      | .inr (t,a) => w t a s := by
  induction k generalizing n j with
  | zero =>
    cases j with
    | inl a => rfl
    | inr p => obtain ⟨t,a⟩ := p; rfl
  | succ k ih =>
    have hih := fun j => ih (n+1) (by omega) j
    cases j with
    | inl a =>
      simp only [continuation, stoppedContinuation]
      apply lintegral_congr; intro x
      rw [hih]
      simp only [taggedStep, dif_pos (show n+1 ≤ T by omega)]
      split_ifs <;> rfl
    | inr p =>
      obtain ⟨t,a⟩ := p
      have hc : ∀ x : Vector d, continuation (taggedStep τ) (taggedWeight w) (n+1) k
          (taggedStep τ (n+1) (.inr (t,a)) (x,⟪s,x⟫)) s = w t a s := fun x => hih _
      simp only [continuation, hc, lintegral_const, measure_univ, mul_one]

