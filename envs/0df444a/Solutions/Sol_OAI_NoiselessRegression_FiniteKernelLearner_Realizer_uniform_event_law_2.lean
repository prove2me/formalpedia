-- Prove2me | solution 2 for OAI.NoiselessRegression.FiniteKernelLearner.Realizer.uniform_event_law
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:35:08.26893+00:00
-- url     : https://prove2.me/submissions/48f5bc63-8fc0-44bc-b906-6a519c0abeba

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Seeded.lean:L17-L40
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.FiniteKernelLearner.Realizer.uniform_event_law. The node keeps its source
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
import Definitions.Def_OAI_Probability_ProjectionMoments_Seeded
import Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_Realizer_conditional_joint_law

-- ---- from OAI.Probability.ProjectionMoments.BorelRules ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace Learner
universe u
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

lemma measurable_countable_select {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    {f : J → X → Y} (hf : ∀ j, Measurable (f j)) {g : X → J} (hg : Measurable g) :
    Measurable (fun x => f (g x) x) :=
  (measurable_from_prod_countable_right (f := fun z : J × X => f z.1 z.2) hf).comp (hg.prodMk measurable_id)

lemma measurable_run (L : Learner d M T Ω) (hL : L.MeasurableRules) (n : ℕ) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.run z.1 z.2.1 z.2.2 n) := by
  classical
  induction n with
  | zero =>
    exact (measurable_of_finite (fun a : Bool × State M =>
      if a.1 then Sum.inr (0,a.2) else Sum.inl a.2)).comp
        (hL.initial.comp (measurable_fst.comp measurable_snd))
  | succ n ih =>
    let F : RunStatus M → (UnitSphere d × (Ω × Samples d T)) → RunStatus M := fun j z =>
      match j with
      | .inr done => .inr done
      | .inl j => if hn : n < T then
          let row := z.2.2 ⟨n,hn⟩
          let a := L.transition (n+1) z.2.1 j (row,⟪row,z.1.val⟫)
          if a.1 then .inr (n+1,a.2) else .inl a.2
        else .inl j
    change Measurable (fun z => F (L.run z.1 z.2.1 z.2.2 n) z)
    apply measurable_countable_select _ ih
    intro j
    cases j with
    | inr done => exact measurable_const
    | inl j =>
      dsimp [F]
      split_ifs with hn
      · exact (measurable_of_finite (fun a : Bool × State M =>
          if a.1 then Sum.inr (n+1,a.2) else Sum.inl a.2)).comp
            ((hL.transition (n+1) j).comp (show Measurable (fun z : UnitSphere d × (Ω × Samples d T) =>
              (z.2.1,(z.2.2 ⟨n,hn⟩,⟪z.2.2 ⟨n,hn⟩,z.1.val⟫))) from by fun_prop))
      · exact measurable_const

lemma measurable_terminal (L : Learner d M T Ω) (hL : L.MeasurableRules) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.terminal z.1 z.2.1 z.2.2) := by
  exact (measurable_of_countable (fun j : RunStatus M =>
    match j with | .inl j => (T,j) | .inr done => done)).comp (L.measurable_run hL T)

lemma measurable_estimate (L : Learner d M T Ω) (hL : L.MeasurableRules) :
    Measurable (fun z : UnitSphere d × (Ω × Samples d T) => L.estimate z.1 z.2.1 z.2.2) := by
  exact measurable_countable_select (f := fun a z => L.output a.1 z.2.1 a.2)
    (fun a => (hL.output a.1 a.2).comp (by fun_prop)) (L.measurable_terminal hL)

end Learner

universe u

namespace Learner
variable {d M T : ℕ} {Ω : Type u} [MeasurableSpace Ω]

end Learner
end NoiselessRegression

end

end OAI

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

lemma Realizer.measurableRules {K : FiniteKernelLearner d M T} (R : K.Realizer) :
    R.toLearner.MeasurableRules := by
  refine ⟨measurable_fst,fun t j => ?_,fun t j => (R.output_measurable t j).comp (by fun_prop)⟩
  dsimp [Realizer.toLearner]
  split_ifs with ht
  · exact (R.transition_measurable t j).comp (show Measurable (fun z : Tape M T × (Vector d × ℝ) =>
      (z.2,z.1.2.1 ⟨t-1,by omega⟩)) from by fun_prop)
  · exact measurable_const

end FiniteKernelLearner

namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

end FiniteKernelLearner
end NoiselessRegression

end

end OAI

-- ---- from OAI.Probability.ProjectionMoments.Seeded ----
namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
namespace NoiselessRegression
namespace FiniteKernelLearner

section
open Learner
variable {d M T : ℕ}

lemma Realizer.uniform_event_law [NeZero d] {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (S : Set (UnitSphere d × Result d M)) (hS : MeasurableSet S) :
    ((uniformSphere d).prod (K.tapeLaw.prod (sampleLaw d T)))
      {z | (z.1,(R.toLearner.terminal z.1 z.2.1 z.2.2,R.toLearner.estimate z.1 z.2.1 z.2.2)) ∈ S} =
    ∫⁻ z : UnitSphere d × Samples d T,
      K.jointExperimentLaw (fun i => (z.2 i,⟪z.1.val,z.2 i⟫))
        {r | (z.1,r) ∈ S} ∂((uniformSphere d).prod (sampleLaw d T)) := by
  have hp := ((MeasurePreserving.id (uniformSphere d)).prod
      (Measure.measurePreserving_swap (μ := sampleLaw d T) (ν := K.tapeLaw))).comp
    (measurePreserving_prodAssoc (uniformSphere d) (sampleLaw d T) K.tapeLaw)
  have hE : MeasurableSet {z : UnitSphere d × (Tape M T × Samples d T) |
      (z.1,(R.toLearner.terminal z.1 z.2.1 z.2.2,R.toLearner.estimate z.1 z.2.1 z.2.2)) ∈ S} :=
    (measurable_fst.prodMk ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules))) hS
  rw [← hp.measure_preimage hE.nullMeasurableSet,Measure.prod_apply (hp.measurable hE)]
  apply lintegral_congr
  intro z
  have hs : MeasurableSet {r : Result d M | (z.1,r) ∈ S} :=
    (measurable_const.prodMk measurable_id) hS
  rw [←R.conditional_joint_law z.1 z.2,Measure.map_apply _ hs]
  · rfl
  · exact ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules)).comp
        (show Measurable (fun ω : Tape M T => (z.1,(ω,z.2))) from by fun_prop)

end

universe u
variable {d M T : ℕ}

end FiniteKernelLearner

end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
open Learner


theorem solution : type_of% @_root_.OAI.NoiselessRegression.FiniteKernelLearner.Realizer.uniform_event_law := @_root_.OAI.NoiselessRegression.FiniteKernelLearner.Realizer.uniform_event_law
