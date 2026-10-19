-- Prove2me | solution 2 for OAI.NoiselessRegression.measurable_coinRun
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:27:26.350856+00:00
-- url     : https://prove2.me/submissions/f4e9513e-c120-4ab0-879c-3c35a2601d3c

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Kernels.lean:L73-L87
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.measurable_coinRun. The node keeps its source
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

-- ---- from OAI.Probability.ProjectionMoments.Kernels ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

namespace FiniteKernelLearner
variable {d M T : ℕ}

end FiniteKernelLearner

variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]

omit [MeasurableSpace O] in
lemma measurable_coinRun [MeasurableSpace O] {F : ℕ → J → O → I → J}
    (hF : ∀ t j obs, Measurable (F t j obs)) (n : ℕ) (j : J) (obs : Fin n → O) :
    Measurable (coinRun F n j obs) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    change Measurable (fun u : Fin (n+1) → I => F (n+1) (coinRun F n j (Fin.init obs) (Fin.init u)) (obs (Fin.last n)) (u (Fin.last n)))
    have hi : Measurable (fun u : Fin (n+1) → I => Fin.init u) := by
      change Measurable (fun u : Fin (n+1) → I => fun i : Fin n => u i.castSucc)
      fun_prop
    have hg : Measurable (fun u : Fin (n+1) → I => coinRun F n j (Fin.init obs) (Fin.init u)) :=
      (ih (Fin.init obs)).comp hi
    exact measurable_select (h := fun a (u : Fin (n+1) → I) => F (n+1) a (obs (Fin.last n)) (u (Fin.last n)))
      (fun a => (hF (n+1) a (obs (Fin.last n))).comp (measurable_pi_apply _)) hg

end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace


theorem solution : type_of% @_root_.OAI.NoiselessRegression.measurable_coinRun := @_root_.OAI.NoiselessRegression.measurable_coinRun
