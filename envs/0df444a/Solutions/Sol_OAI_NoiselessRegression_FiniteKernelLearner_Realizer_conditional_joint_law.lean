-- Prove2me | solution 1 for OAI.NoiselessRegression.FiniteKernelLearner.Realizer.conditional_joint_law
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T19:46:42.933732+00:00
-- url     : https://prove2.me/submissions/7fd4e4af-b54c-4ca6-9d6d-e7ee755c54e4

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
theorem nr_meas {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {F : ℕ → J → O → I → J}
    (hF : ∀ t j obs, Measurable (F t j obs)) (n : ℕ) (j : J) (obs : Fin n → O) :
    Measurable (coinRun F n j obs) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    have hG : Measurable fun p : J × I => F (n+1) p.1 (obs (Fin.last n)) p.2 :=
      measurable_from_prod_countable_right (fun x => hF _ _ _)
    have hinit : Measurable (fun u : Fin (n+1) → I => Fin.init u) :=
      measurable_pi_lambda _ (fun i => measurable_pi_apply _)
    exact hG.comp (((ih (Fin.init obs)).comp hinit).prodMk (measurable_pi_apply _))

theorem nr_lintegral_coinRun {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
    {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
    (hF : ∀ t j obs, Measurable (F t j obs))
    (hP : ∀ t j obs, volume.map (F t j obs) = P t j obs)
    (n : ℕ) (j : J) (obs : Fin n → O) (f : J → ℝ≥0∞) :
    (∫⁻ u, f (coinRun F n j obs u) ∂Measure.pi (fun _ => (volume : Measure I))) =
      ∫⁻ a, f a ∂kernelRun P n j obs := by
  induction n generalizing f with
  | zero =>
    simp only [kernelRun, lintegral_dirac' _ (measurable_of_finite f)]
    rw [show (fun u : Fin 0 → I => f (coinRun F 0 j obs u)) = fun _ => f j from rfl]
    simp
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => I) (Fin.last n)
    have hmp : MeasurePreserving e (Measure.pi (fun _ => (volume : Measure I)))
        ((volume : Measure I).prod (Measure.pi (fun _ : Fin n => (volume : Measure I)))) :=
      measurePreserving_piFinSuccAbove (fun _ => volume) (Fin.last n)
    have hsymm : ∀ q : I × (Fin n → I), e.symm q = Fin.snoc q.2 q.1 := by
      rintro ⟨x, v⟩
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
    have hrun : ∀ q : I × (Fin n → I), coinRun F (n+1) j obs (e.symm q) =
        F (n+1) (coinRun F n j (Fin.init obs) q.2) (obs (Fin.last n)) q.1 := by
      intro q; rw [hsymm]; simp [coinRun, Fin.init_snoc, Fin.snoc_last]
    rw [← hmp.symm.lintegral_comp_emb e.symm.measurableEmbedding]
    simp only [hrun]
    have hG : Measurable fun q : I × (Fin n → I) =>
        f (F (n+1) (coinRun F n j (Fin.init obs) q.2) (obs (Fin.last n)) q.1) := by
      have h1 : Measurable fun p : I × J => F (n+1) p.2 (obs (Fin.last n)) p.1 :=
        measurable_from_prod_countable_left (fun y => hF _ _ _)
      exact (measurable_of_finite f).comp (h1.comp (measurable_fst.prodMk
        ((nr_meas hF n j (Fin.init obs)).comp measurable_snd)))
    rw [lintegral_prod_symm _ hG.aemeasurable]
    have hinner : ∀ a : J, ∫⁻ x, f (F (n+1) a (obs (Fin.last n)) x) ∂(volume : Measure I) =
        ∫⁻ b, f b ∂P (n+1) a (obs (Fin.last n)) := by
      intro a
      rw [← hP, lintegral_map (measurable_of_finite f) (hF _ _ _)]
    simp only [hinner]
    rw [ih (Fin.init obs) (fun a => ∫⁻ b, f b ∂P (n+1) a (obs (Fin.last n)))]
    simp only [kernelRun]
    rw [Measure.lintegral_bind (measurable_of_finite _).aemeasurable (measurable_of_finite f).aemeasurable]

theorem nr_run_eq {K : FiniteKernelLearner d M T} (R : K.Realizer)
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

theorem nr_terminal {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (ω : Tape M T) (x : Samples d T) :
    (R.toLearner.terminal s ω x, R.toLearner.estimate s ω x) =
      R.terminalJointOutput (coinRun R.taggedTransition T (taggedStart ω.1)
        (fun i => (x i,⟪s.val,x i⟫)) ω.2.1) ω.2.2 := by
  have h := nr_run_eq R s ω x (le_refl T)
  simp only [Learner.estimate, Learner.terminal, h]
  show _ = R.terminalJointOutput (coinRun R.taggedTransition T (taggedStart ω.1)
        (fun i => (x (Fin.castLE (le_refl T) i),⟪s.val,x (Fin.castLE (le_refl T) i)⟫))
        (fun i => ω.2.1 (Fin.castLE (le_refl T) i))) ω.2.2
  generalize coinRun R.taggedTransition T (taggedStart ω.1)
        (fun i => (x (Fin.castLE (le_refl T) i),⟪s.val,x (Fin.castLE (le_refl T) i)⟫))
        (fun i => ω.2.1 (Fin.castLE (le_refl T) i)) = c
  cases c with
  | inl j => rfl
  | inr p => obtain ⟨t,j⟩ := p; rfl

theorem nr_tt_meas {K : FiniteKernelLearner d M T} (R : K.Realizer) (t : ℕ)
    (j : TaggedState M T) (obs : Vector d × ℝ) : Measurable (R.taggedTransition t j obs) := by
  cases j with
  | inr a => exact measurable_const
  | inl j =>
    by_cases ht : t ≤ T
    · have h1 : Measurable (R.transition t j obs) :=
        (R.transition_measurable t j).comp (measurable_const.prodMk measurable_id)
      have : R.taggedTransition t (.inl j) obs = fun u => destination t ht (R.transition t j obs u) := by
        funext u; simp [Realizer.taggedTransition, ht]
      rw [this]
      exact (measurable_of_countable (destination t ht : Bool × State M → TaggedState M T)).comp h1
    · have : R.taggedTransition t (.inl j) obs = fun _ => .inl j := by
        funext u; simp [Realizer.taggedTransition, ht]
      rw [this]; exact measurable_const

theorem nr_tt_law {K : FiniteKernelLearner d M T} (R : K.Realizer) (t : ℕ)
    (j : TaggedState M T) (obs : Vector d × ℝ) :
    volume.map (R.taggedTransition t j obs) = K.taggedKernel t j obs := by
  cases j with
  | inr a =>
    have : R.taggedTransition t (.inr a) obs = fun _ => .inr a := rfl
    rw [this, Measure.map_const]; simp [taggedKernel]
  | inl j =>
    by_cases ht : t ≤ T
    · have h1 : Measurable (R.transition t j obs) :=
        (R.transition_measurable t j).comp (measurable_const.prodMk measurable_id)
      have : R.taggedTransition t (.inl j) obs = (destination t ht) ∘ (R.transition t j obs) := by
        funext u; simp [Realizer.taggedTransition, ht]
      rw [this, ← Measure.map_map (measurable_of_countable (destination t ht : Bool × State M → TaggedState M T)) h1, R.transition_law]
      simp [taggedKernel, ht]
    · have : R.taggedTransition t (.inl j) obs = fun _ => .inl j := by
        funext u; simp [Realizer.taggedTransition, ht]
      rw [this, Measure.map_const]; simp [taggedKernel, ht]

theorem nr_tjo_law {K : FiniteKernelLearner d M T} (R : K.Realizer) (j : TaggedState M T) :
    volume.map (R.terminalJointOutput j) = K.terminalJointOutput j := by
  cases j with
  | inl j =>
    have : R.terminalJointOutput (.inl j) = (fun y => (terminalTag (T := T) (.inl j), y)) ∘ R.output T j := rfl
    rw [this, ← Measure.map_map (by fun_prop) (R.output_measurable _ _), R.output_law]; rfl
  | inr p =>
    obtain ⟨t,j⟩ := p
    have : R.terminalJointOutput (.inr (t,j)) = (fun y => (terminalTag (T := T) (.inr (t,j)), y)) ∘ R.output t j := rfl
    rw [this, ← Measure.map_map (by fun_prop) (R.output_measurable _ _), R.output_law]; rfl

theorem nr_tjo_meas {K : FiniteKernelLearner d M T} (R : K.Realizer) (j : TaggedState M T) :
    Measurable (R.terminalJointOutput j) := by
  cases j with
  | inl j => exact measurable_const.prodMk (R.output_measurable _ _)
  | inr p => obtain ⟨t,j⟩ := p; exact measurable_const.prodMk (R.output_measurable _ _)

theorem solution {K : FiniteKernelLearner d M T} (R : K.Realizer)
    (s : UnitSphere d) (x : Samples d T) :
    K.tapeLaw.map (fun ω => (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) =
      K.jointExperimentLaw (fun i => (x i,⟪s.val,x i⟫)) := by
  have := K.initial_probability
  set obs : Fin T → Vector d × ℝ := fun i => (x i,⟪s.val,x i⟫) with hobs
  have hf : (fun ω => (R.toLearner.terminal s ω x,R.toLearner.estimate s ω x)) =
      fun ω : Tape M T => R.terminalJointOutput (coinRun R.taggedTransition T (taggedStart ω.1) obs ω.2.1) ω.2.2 := by
    funext ω; exact nr_terminal R s ω x
  rw [hf]
  have hmeas : Measurable (fun ω : Tape M T => R.terminalJointOutput (coinRun R.taggedTransition T (taggedStart ω.1) obs ω.2.1) ω.2.2) := by
    apply measurable_from_prod_countable_right
    intro a
    have h1 : Measurable fun p : TaggedState M T × I => R.terminalJointOutput p.1 p.2 :=
      measurable_from_prod_countable_right (fun j => nr_tjo_meas R j)
    exact h1.comp (((nr_meas (nr_tt_meas R) T (taggedStart a) obs).comp measurable_fst).prodMk measurable_snd)
  ext S hS
  rw [Measure.map_apply hmeas hS]
  unfold jointExperimentLaw
  rw [Measure.bind_apply hS (measurable_of_countable _).aemeasurable]
  unfold tapeLaw
  rw [← lintegral_indicator_one (hmeas hS), lintegral_prod _ (measurable_one.indicator (hmeas hS)).aemeasurable]
  apply lintegral_congr; intro a
  rw [Measure.bind_apply hS (measurable_of_countable _).aemeasurable]
  have hm2 : Measurable (fun q : (Fin T → I) × I =>
      S.indicator 1 (R.terminalJointOutput (coinRun R.taggedTransition T (taggedStart a) obs q.1) q.2) : _ → ℝ≥0∞) := by
    have h1 : Measurable fun p : TaggedState M T × I => R.terminalJointOutput p.1 p.2 :=
      measurable_from_prod_countable_right (fun j => nr_tjo_meas R j)
    exact (measurable_one.indicator hS).comp (h1.comp (((nr_meas (nr_tt_meas R) T (taggedStart a) obs).comp measurable_fst).prodMk measurable_snd))
  have hcomp : (fun ω : (Fin T → I) × I => S.indicator (1 : Result d M → ℝ≥0∞)
      (R.terminalJointOutput (coinRun R.taggedTransition T (taggedStart a) obs ω.1) ω.2)) =
      (fun ω : (Fin T → I) × I => S.indicator (1 : Result d M → ℝ≥0∞)
      (R.terminalJointOutput (coinRun R.taggedTransition T (taggedStart a) obs ω.1) ω.2)) := rfl
  show ∫⁻ q : (Fin T → I) × I, S.indicator (1 : Result d M → ℝ≥0∞) (R.terminalJointOutput (coinRun R.taggedTransition T (taggedStart a) obs q.1) q.2) ∂((Measure.pi fun _ => (volume : Measure I)).prod volume) = _
  rw [lintegral_prod _ hm2.aemeasurable]
  have hin : ∀ j : TaggedState M T, ∫⁻ v, S.indicator (1 : Result d M → ℝ≥0∞) (R.terminalJointOutput j v) ∂(volume : Measure I) =
      K.terminalJointOutput j S := by
    intro j
    rw [← nr_tjo_law R j, Measure.map_apply (nr_tjo_meas R j) hS,
      ← lintegral_indicator_one ((nr_tjo_meas R j) hS)]
    rfl
  simp only [hin]
  exact nr_lintegral_coinRun (nr_tt_meas R) (nr_tt_law R) T _ obs (fun j => K.terminalJointOutput j S)

