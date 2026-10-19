-- Prove2me | solution 1 for OAI.NoiselessRegression.lintegral_coinRun
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T18:46:14.788374+00:00
-- url     : https://prove2.me/submissions/01ab7ef2-c92c-4e42-b635-d0aab57c00f9

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

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open MeasureTheory ProbabilityTheory Set Filter unitInterval
open scoped ENNReal NNReal RealInnerProductSpace
variable {J O : Type*} [Fintype J] [MeasurableSpace J] [MeasurableSingletonClass J]
  [MeasurableSpace O]
theorem nr_meas [MeasurableSpace O] {F : ℕ → J → O → I → J}
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


theorem solution {F : ℕ → J → O → I → J} {P : ℕ → J → O → Measure J}
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
