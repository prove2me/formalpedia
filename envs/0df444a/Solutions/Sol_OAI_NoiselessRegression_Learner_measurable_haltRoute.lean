-- Prove2me | solution 1 for OAI.NoiselessRegression.Learner.measurable_haltRoute
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:40:41.595844+00:00
-- url     : https://prove2.me/submissions/113ca621-7008-4656-bde0-7a9c625d8835

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
variable {d M : ℕ}


theorem solution {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (n k : ℕ) (j : State M) :
    Measurable (haltRoute τ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    let G : (Bool × State M) × ((Fin k → Vector d) × (Fin k → ℝ)) → TaggedState M (k+1) :=
      fun p => if p.1.1 then .inr (⟨1,by omega⟩,p.1.2)
        else haltShift (haltRoute τ (n+1) k p.1.2 p.2)
    have hG : Measurable G := by
      apply measurable_from_prod_countable_right
      intro a
      by_cases ha : a.1
      · simp only [G, ha, if_true]; exact measurable_const
      · simp only [G, ha]
        exact (measurable_from_top (f := (haltShift : TaggedState M k → TaggedState M (k+1)))).comp (ih (n+1) a.2)
    have hT : Measurable (fun X : (Fin (k+1) → Vector d) × (Fin (k+1) → ℝ) => Fin.tail X.1) :=
      measurable_pi_lambda _ (fun i => (measurable_pi_apply _).comp measurable_fst)
    have hT2 : Measurable (fun X : (Fin (k+1) → Vector d) × (Fin (k+1) → ℝ) => Fin.tail X.2) :=
      measurable_pi_lambda _ (fun i => (measurable_pi_apply _).comp measurable_snd)
    have h0 : Measurable (fun X : (Fin (k+1) → Vector d) × (Fin (k+1) → ℝ) => (X.1 0, X.2 0)) :=
      ((measurable_pi_apply _).comp measurable_fst).prodMk ((measurable_pi_apply _).comp measurable_snd)
    have heq : haltRoute τ n (k+1) j = G ∘ (fun X => (τ (n+1) j (X.1 0, X.2 0), (Fin.tail X.1, Fin.tail X.2))) := by
      funext X; rfl
    rw [heq]
    exact hG.comp (((hτ _ _).comp h0).prodMk (hT.prodMk hT2))

