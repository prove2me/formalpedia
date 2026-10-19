-- Prove2me | solution 2 for OAI.NoiselessRegression.FiniteKernelLearner.Realizer.run_eq_coinRun
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:32:30.793504+00:00
-- url     : https://prove2.me/submissions/4b645538-5cfe-428f-aef4-4a3fd560373b

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Realization.lean:L117-L138
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.FiniteKernelLearner.Realizer.run_eq_coinRun. The node keeps its source
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

-- ---- from OAI.Probability.GaussianRegression.Execution ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
Finite-state sequential execution and terminal-state witnesses.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
open scoped Pointwise

noncomputable section

universe u

namespace NoiselessRegression

lemma fin_prefix_snoc {X : Type*} {n T : ℕ} (h : n+1 ≤ T) (x : Fin T → X) :
    (fun i : Fin (n+1) => x (Fin.castLE h i)) =
      (Fin.snoc (fun i : Fin n => x (Fin.castLE (by omega) i))
        (x ⟨n, by omega⟩) : Fin (n+1) → X) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    rfl
  · simp

namespace Learner
variable {d M T : ℕ} {Ω : Type u} (L : Learner d M T Ω)

end Learner

end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Stopping ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable {J : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]

variable [Nontrivial E] [Nonempty J]

end

namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u}

lemma decode_taggedStart (a : Bool × State M) :
    decodeTagged (taggedStart (T := T) a) = if a.1 then .inr (0,a.2) else .inl a.2 := by
  simp only [taggedStart]; split_ifs <;> rfl

end Learner
end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Realization ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

lemma Realizer.run_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) {n : ℕ} (hn : n ≤ T) :
    R.toLearner.run s ω x n = decodeTagged
      (coinRun R.taggedTransition n (taggedStart ω.1)
        (fun i => (x (Fin.castLE hn i),⟪s.val,x (Fin.castLE hn i)⟫))
        (fun i => ω.2.1 (Fin.castLE hn i))) := by
  induction n with
  | zero => exact (decode_taggedStart _).symm
  | succ n ih =>
    rw [Learner.run,ih (by omega)]
    have hp := fin_prefix_snoc hn (fun i => (x i,⟪s.val,x i⟫))
    rw [hp,fin_prefix_snoc hn ω.2.1,coinRun,Fin.init_snoc,Fin.init_snoc,Fin.snoc_last,Fin.snoc_last]
    generalize coinRun R.taggedTransition n (taggedStart ω.1)
      (fun i => (x (Fin.castLE (by omega : n ≤ T) i),⟪s.val,x (Fin.castLE (by omega : n ≤ T) i)⟫))
      (fun i => ω.2.1 (Fin.castLE (by omega : n ≤ T) i)) = j
    cases j with
    | inr a => rfl
    | inl j =>
      simp only [decodeTagged,Realizer.taggedTransition,Realizer.toLearner,
        dite_eq_left (by omega : n < T),dite_eq_left (by omega : 0 < n+1 ∧ n+1 ≤ T),
        dite_eq_left (by omega : n+1 ≤ T),destination,real_inner_comm,Nat.add_sub_cancel]
      split_ifs <;> rfl

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


theorem solution : type_of% @_root_.OAI.NoiselessRegression.FiniteKernelLearner.Realizer.run_eq_coinRun := @_root_.OAI.NoiselessRegression.FiniteKernelLearner.Realizer.run_eq_coinRun
