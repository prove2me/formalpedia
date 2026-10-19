-- Prove2me | solution 1 for OAI.NoiselessRegression.FiniteKernelLearner.Realizer.run_eq_coinRun
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:42:59.904012+00:00
-- url     : https://prove2.me/submissions/9ea6f88c-d023-4c90-a24a-53a1ca6fbd1d

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


theorem solution {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) {n : ℕ} (hn : n ≤ T) :
    R.toLearner.run s ω x n = decodeTagged
      (coinRun R.taggedTransition n (taggedStart ω.1)
        (fun i => (x (Fin.castLE hn i),⟪s.val,x (Fin.castLE hn i)⟫))
        (fun i => ω.2.1 (Fin.castLE hn i))) := by
  induction n with
  | zero =>
    show R.toLearner.start ω = decodeTagged (taggedStart ω.1)
    by_cases h : ω.1.1 <;> simp [Learner.start, taggedStart, Realizer.toLearner, h, decodeTagged]
  | succ n ih =>
    have ih' := ih (by omega)
    have hc : coinRun R.taggedTransition (n+1) (taggedStart ω.1)
        (fun i => (x (Fin.castLE hn i),⟪s.val,x (Fin.castLE hn i)⟫))
        (fun i => ω.2.1 (Fin.castLE hn i)) =
        R.taggedTransition (n+1) (coinRun R.taggedTransition n (taggedStart ω.1)
          (fun i => (x (Fin.castLE (by omega) i),⟪s.val,x (Fin.castLE (by omega) i)⟫))
          (fun i => ω.2.1 (Fin.castLE (by omega) i)))
          (x ⟨n,by omega⟩,⟪s.val,x ⟨n,by omega⟩⟫) (ω.2.1 ⟨n,by omega⟩) := rfl
    rw [hc]
    simp only [Learner.run]
    rw [ih']
    generalize coinRun R.taggedTransition n (taggedStart ω.1)
          (fun i => (x (Fin.castLE (by omega) i),⟪s.val,x (Fin.castLE (by omega) i)⟫))
          (fun i => ω.2.1 (Fin.castLE (by omega) i)) = c
    cases c with
    | inl j =>
      simp only [decodeTagged, Realizer.taggedTransition, dif_pos (show n < T by omega),
        dif_pos (show n+1 ≤ T by omega), destination, Realizer.toLearner,
        dif_pos (show 0 < n+1 ∧ n+1 ≤ T by omega), real_inner_comm (x ⟨n,_⟩) s.val, Nat.add_sub_cancel]
      split_ifs <;> rfl
    | inr p =>
      obtain ⟨t,j⟩ := p
      rfl

