-- Prove2me | solution 2 for OAI.NoiselessRegression.FiniteKernelLearner.Realizer.conditional_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T20:34:22.013982+00:00
-- url     : https://prove2.me/submissions/59ef0d1a-e6e9-49d4-ba5e-04b71edec3c5

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Realization.lean:L215-L244
-- (upload_full_project.md Phase 4): solution for node OAI.NoiselessRegression.FiniteKernelLearner.Realizer.conditional_joint_law. The node keeps its source
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
import Theorems.Thm_OAI_NoiselessRegression_FiniteKernelLearner_Realizer_run_eq_coinRun
import Theorems.Thm_OAI_NoiselessRegression_lintegral_coinRun
import Theorems.Thm_OAI_NoiselessRegression_measurable_coinRun

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

lemma Realizer.tagged_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ) : Measurable (R.taggedTransition t j obs) := by
  cases j with
  | inr a => exact measurable_const
  | inl j =>
    change Measurable (fun u => R.taggedTransition t (.inl j) obs u)
    simp only [Realizer.taggedTransition]
    split_ifs with ht
    · exact (measurable_of_finite (destination t ht)).comp (R.transition_measurable t j).of_uncurry_left
    · exact measurable_const

lemma Realizer.tagged_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (t : ℕ) (j : TaggedState M T) (obs : Vector d × ℝ) :
    volume.map (R.taggedTransition t j obs) = K.taggedKernel t j obs := by
  cases j with
  | inr a =>
    change volume.map (fun _ : I => Sum.inr a) = Measure.dirac (.inr a)
    simp [Measure.map_const]
  | inl j =>
    change volume.map (fun u => R.taggedTransition t (.inl j) obs u) = _
    simp only [Realizer.taggedTransition,taggedKernel]
    split_ifs with ht
    · rw [← R.transition_law,Measure.map_map (measurable_of_finite _)
        (R.transition_measurable t j).of_uncurry_left]
      rfl
    · simp [Measure.map_const]

lemma Realizer.terminalOutput_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : Measurable (R.terminalOutput j) := by
  cases j with
  | inl j => exact R.output_measurable T j
  | inr a => exact R.output_measurable a.1 a.2

lemma Realizer.terminalOutput_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : volume.map (R.terminalOutput j) = K.terminalOutput j := by
  cases j with
  | inl j => exact R.output_law T j
  | inr a => exact R.output_law a.1 a.2

lemma Realizer.estimate_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) :
    R.toLearner.estimate s ω x = R.terminalOutput
      (coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1) ω.2.2 := by
  unfold Learner.estimate Learner.terminal
  rw [R.run_eq_coinRun s ω x le_rfl]
  have hi (i : Fin T) : Fin.castLE le_rfl i = i := Fin.ext rfl
  simp only [hi]
  generalize coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1 = j
  cases j <;> rfl

end FiniteKernelLearner

lemma map_finite_prod_eq_bind {A B C : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) [SFinite ν] {f : A × B → C} (hf : Measurable f) :
    (μ.prod ν).map f = μ.bind (fun a => ν.map (fun b => f (a,b))) := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map hg hf,lintegral_prod (fun z => g (f z)) (hg.comp hf).aemeasurable,
    Measure.lintegral_bind (measurable_of_finite _).aemeasurable hg.aemeasurable]
  apply lintegral_congr
  intro a
  exact (lintegral_map hg (hf.comp (measurable_const.prodMk measurable_id))).symm

lemma coinRun_output_law {J O Y : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J] [MeasurableSpace O] [MeasurableSpace Y]
    {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    {g : J → I → Y} {Q : J → Measure Y} (hg : ∀ j, Measurable (g j))
    (hQ : ∀ j, volume.map (g j) = Q j) (n : ℕ) (j : J) (obs : Fin n → O) :
    ((Measure.pi (fun _ => (volume : Measure I))).prod volume).map
      (fun z => g (coinRun F n j obs z.1) z.2) = (kernelRun P n j obs).bind Q := by
  have hm : Measurable (fun z : (Fin n → I) × I => g (coinRun F n j obs z.1) z.2) :=
    measurable_select (h := fun a (z : (Fin n → I) × I) => g a z.2)
      (fun a => (hg a).comp measurable_snd) ((measurable_coinRun hF n j obs).comp measurable_fst)
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hm,lintegral_prod (fun z => f (g (coinRun F n j obs z.1) z.2)) (hf.comp hm).aemeasurable]
  have ho (a : J) : (∫⁻ u, f (g a u) ∂volume) = ∫⁻ y, f y ∂Q a := by
    rw [← hQ]
    exact (lintegral_map hf (hg a)).symm
  simp_rw [ho]
  rw [lintegral_coinRun hF hP n j obs (fun a => ∫⁻ y, f y ∂Q a)]
  exact (Measure.lintegral_bind (measurable_of_finite _).aemeasurable hf.aemeasurable).symm

namespace FiniteKernelLearner
open Learner
variable {d M T : ℕ}

lemma Realizer.terminalJointOutput_measurable {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : Measurable (R.terminalJointOutput j) :=
  measurable_const.prodMk (R.terminalOutput_measurable j)

lemma Realizer.terminalJointOutput_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (j : TaggedState M T) : volume.map (R.terminalJointOutput j) = K.terminalJointOutput j := by
  rw [FiniteKernelLearner.terminalJointOutput,← R.terminalOutput_law,
    Measure.map_map (by fun_prop) (R.terminalOutput_measurable j)]
  rfl

lemma Realizer.terminal_eq_coinRun {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) :
    R.toLearner.terminal s ω x = terminalTag
      (coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1) := by
  unfold Learner.terminal
  rw [R.run_eq_coinRun s ω x le_rfl]
  have hi (i : Fin T) : Fin.castLE le_rfl i = i := Fin.ext rfl
  simp only [hi]
  generalize coinRun R.taggedTransition T (taggedStart ω.1) (fun i => (x i,⟪s.val,x i⟫)) ω.2.1 = j
  cases j <;> rfl

theorem Realizer.conditional_joint_law {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (x : Samples d T) :
    K.tapeLaw.map (fun ω => (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) =
      K.jointExperimentLaw (fun i => (x i,⟪s.val,x i⟫)) := by
  have hm : Measurable (fun ω : Tape M T =>
      (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) :=
    ((R.toLearner.measurable_terminal R.measurableRules).prodMk
      (R.toLearner.measurable_estimate R.measurableRules)).comp
        (show Measurable (fun ω : Tape M T => (s,(ω,x))) from by fun_prop)
  unfold tapeLaw jointExperimentLaw
  have : IsProbabilityMeasure ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := inferInstance
  have : IsFiniteMeasure ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := inferInstance
  have : SigmaFinite ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod
      (volume : Measure I)) := IsFiniteMeasure.toSigmaFinite _
  rw [map_finite_prod_eq_bind K.initial
    ((Measure.pi (fun _ : Fin T => (volume : Measure I))).prod (volume : Measure I)) hm]
  congr 1
  funext a
  have he : (fun z : (Fin T → I) × I =>
      (R.toLearner.terminal s (a,z) x,R.toLearner.estimate s (a,z) x)) =
      (fun z => R.terminalJointOutput
        (coinRun R.taggedTransition T (taggedStart a) (fun i => (x i,⟪s.val,x i⟫)) z.1) z.2) := by
    funext z
    rw [R.terminal_eq_coinRun,R.estimate_eq_coinRun]
    rfl
  rw [he]
  exact coinRun_output_law R.tagged_measurable R.tagged_law R.terminalJointOutput_measurable
    R.terminalJointOutput_law T (taggedStart a) _

end FiniteKernelLearner
end NoiselessRegression

end

end OAI

-- ---- platform node ----
open OAI OAI.NoiselessRegression OAI.NoiselessRegression.FiniteKernelLearner
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
open Learner


theorem solution : type_of% @_root_.OAI.NoiselessRegression.FiniteKernelLearner.Realizer.conditional_joint_law := @_root_.OAI.NoiselessRegression.FiniteKernelLearner.Realizer.conditional_joint_law
