-- Prove2me | solution 2 for OAI.NoiselessRegression.Learner.measurable_haltRoute
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:40:46.998079+00:00
-- url     : https://prove2.me/submissions/86e0bb0c-fa37-4c44-b7b0-1e97f83c04cd

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/StoppingKernel.lean:L131-L149
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.Learner.measurable_haltRoute. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_StoppingKernel

-- ---- from OAI.Probability.GaussianRegression.Stream ----
namespace OAI

/-!
Sequential routing and continuation mass propagation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

section StreamAux
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

lemma measurable_select {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {h : J → X → Y} (hh : ∀ j, Measurable (h j)) {φ : X → J} (hφ : Measurable φ) :
    Measurable (fun x => h (φ x) x) :=
  (measurable_from_prod_countable_right (f := fun p : J × X => h p.1 p.2) hh).comp (hφ.prodMk measurable_id)

end StreamAux

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.StoppingKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J] [Nonempty J]

end

namespace Learner

section
variable {d M : ℕ}

lemma measurable_haltRoute {τ : ℕ → State M → (Vector d × ℝ) → Bool × State M}
    (hτ : ∀ t j, Measurable (τ t j)) (n k : ℕ) (j : State M) :
    Measurable (haltRoute τ n k j) := by
  induction k generalizing n j with
  | zero => exact measurable_const
  | succ k ih =>
    let h : (Bool × State M) → ((Fin (k+1) → Vector d) × (Fin (k+1) → ℝ)) → TaggedState M (k+1) :=
      fun a X => if a.1 then .inr (⟨1,by omega⟩,a.2)
        else haltShift (haltRoute τ (n+1) k a.2 (Fin.tail X.1,Fin.tail X.2))
    change Measurable (fun X => h (τ (n+1) j (X.1 0,X.2 0)) X)
    apply measurable_select (J := Bool × State M) _ ((hτ (n+1) j).comp (by fun_prop))
    intro a
    dsimp [h]
    split_ifs
    · exact measurable_const
    · exact (measurable_of_finite haltShift).comp ((ih (n+1) a.2).comp (by
        change Measurable (fun X : ((Fin (k+1) → Vector d) × (Fin (k+1) → ℝ)) =>
          ((fun i : Fin k => X.1 i.succ),(fun i : Fin k => X.2 i.succ)))
        fun_prop))

end

variable {d M T : ℕ}

variable [NeZero d]

end Learner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.Learner
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.NoiselessRegression.Learner.measurable_haltRoute := @_root_.OAI.NoiselessRegression.Learner.measurable_haltRoute
