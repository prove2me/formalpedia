-- Prove2me | solution 1 for Kyprianou.Ch05.killedPotential_lintegral_formula
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T10:11:11.526618+00:00
-- url     : https://prove2.me/submissions/81c05802-7454-45d3-802b-4d58b1629ee3

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_lintegral_formula_indicator
import Theorems.Thm_Kyprianou_Ch05_killedPotential_inner_aemeasurable
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (death : Omega → WithTop NNReal)
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hKilled : Kyprianou.Ch05.IsKilledSubordinator P Y death eta)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi)
    (hLaplaceLaw : ∀ (t : NNReal) (theta : Real), 0 ≤ theta →
      (∫ omega, Real.exp (-theta * Y t omega) ∂P) =
        Real.exp (-(t : Real) * (Phi theta - eta)))
    (U : Real → Measure Real)
    (hPotential : Kyprianou.Ch05.IsKilledPotentialFamily P Y death U) :
  ∀ q : Real, 0 ≤ q → ∀ f : Real → ENNReal, Measurable f →
      (∫⁻ x : Real, f x ∂(U q)) =
        ∫⁻ t in Set.Ici (0 : Real),
          ENNReal.ofReal (Real.exp (-q * t)) *
          ∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
            f (Y (Real.toNNReal t) omega) ∂P ∂volume := by
  intro q hq f hf
  have hYAEMeas : ∀ s : NNReal, AEMeasurable (Y s) P := by
    intro s
    have h := (hKilled.1.1.stationary_increments 0 s).1
    have hinc : ProbabilityTheory.increment Y 0 (0 + s) = Y s := by
      funext ω
      simp [ProbabilityTheory.increment, hKilled.1.1.start_zero]
    rwa [hinc] at h
  have hinnerAE : ∀ (g : Real → ENNReal), Measurable g → ∀ t : Real,
      AEMeasurable (fun omega : Omega => g (Y (Real.toNNReal t) omega))
        (P.restrict {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega}) :=
    fun g hg t => hg.comp_aemeasurable
      ((hYAEMeas (Real.toNNReal t)).mono_measure Measure.restrict_le_self)
  have hcmeas : Measurable (fun t : Real => ENNReal.ofReal (Real.exp (-q * t))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul _))
  have houterAE : ∀ (g : Real → ENNReal), Measurable g →
      AEMeasurable (fun t : Real => ENNReal.ofReal (Real.exp (-q * t)) *
        ∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
          g (Y (Real.toNNReal t) omega) ∂P) (volume.restrict (Set.Ici (0 : Real))) :=
    fun g hg => hcmeas.aemeasurable.mul
      (Kyprianou.Ch05.killedPotential_inner_aemeasurable P Y death eta d Pi Phi
        hKilled hTriplet hLaplaceLaw U hPotential g hg)
  refine Measurable.ennreal_induction (motive := fun f : Real → ENNReal =>
    (∫⁻ x : Real, f x ∂(U q)) =
      ∫⁻ t in Set.Ici (0 : Real),
        ENNReal.ofReal (Real.exp (-q * t)) *
        ∫⁻ omega in {omega : Omega |
          (Real.toNNReal t : WithTop NNReal) < death omega},
          f (Y (Real.toNNReal t) omega) ∂P ∂volume) ?_ ?_ ?_ hf
  · -- Indicator case: the published child.
    intro c B hB
    exact Kyprianou.Ch05.killedPotential_lintegral_formula_indicator
      P Y death eta d Pi Phi hKilled hTriplet hLaplaceLaw U hPotential q hq c B hB
  · -- Addition of disjointly supported functions.
    intro f g _hdisj hf hg ihf ihg
    have hsplit : ∀ t : Real,
        (∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
          (f + g) (Y (Real.toNNReal t) omega) ∂P)
        = (∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
            f (Y (Real.toNNReal t) omega) ∂P)
          + (∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
            g (Y (Real.toNNReal t) omega) ∂P) := by
      intro t
      exact MeasureTheory.lintegral_add_left' (hinnerAE f hf t) _
    calc (∫⁻ x : Real, (f + g) x ∂(U q))
        = (∫⁻ x : Real, f x ∂(U q)) + (∫⁻ x : Real, g x ∂(U q)) :=
          MeasureTheory.lintegral_add_left' hf.aemeasurable _
      _ = (∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
            ∫⁻ omega in {omega : Omega |
              (Real.toNNReal t : WithTop NNReal) < death omega},
              f (Y (Real.toNNReal t) omega) ∂P ∂volume)
          + (∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
            ∫⁻ omega in {omega : Omega |
              (Real.toNNReal t : WithTop NNReal) < death omega},
              g (Y (Real.toNNReal t) omega) ∂P ∂volume) := by rw [ihf, ihg]
      _ = ∫⁻ t in Set.Ici (0 : Real),
            (ENNReal.ofReal (Real.exp (-q * t)) *
              ∫⁻ omega in {omega : Omega |
                (Real.toNNReal t : WithTop NNReal) < death omega},
                f (Y (Real.toNNReal t) omega) ∂P
            + ENNReal.ofReal (Real.exp (-q * t)) *
              ∫⁻ omega in {omega : Omega |
                (Real.toNNReal t : WithTop NNReal) < death omega},
                g (Y (Real.toNNReal t) omega) ∂P) ∂volume :=
          (MeasureTheory.lintegral_add_left' (houterAE f hf) _).symm
      _ = ∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
            ∫⁻ omega in {omega : Omega |
              (Real.toNNReal t : WithTop NNReal) < death omega},
              (f + g) (Y (Real.toNNReal t) omega) ∂P ∂volume := by
          refine MeasureTheory.lintegral_congr fun t => ?_
          rw [hsplit t]
          exact (mul_add _ _ _).symm
  · -- Supremum of an increasing sequence.
    intro f hf hmono ih
    have hinner_iSup : ∀ t : Real,
        (∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
          (fun x : Real => ⨆ n, f n x) (Y (Real.toNNReal t) omega) ∂P)
        = ⨆ n, ∫⁻ omega in {omega : Omega |
            (Real.toNNReal t : WithTop NNReal) < death omega},
            f n (Y (Real.toNNReal t) omega) ∂P := by
      intro t
      simp only [iSup_apply]
      refine MeasureTheory.lintegral_iSup' (fun n => hinnerAE (f n) (hf n) t) ?_
      filter_upwards with omega n m hnm
      exact hmono hnm _
    calc (∫⁻ x : Real, (fun x : Real => ⨆ n, f n x) x ∂(U q))
        = ⨆ n, ∫⁻ x : Real, f n x ∂(U q) := by
          simp only [iSup_apply]
          exact MeasureTheory.lintegral_iSup hf hmono
      _ = ⨆ n, ∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
            ∫⁻ omega in {omega : Omega |
              (Real.toNNReal t : WithTop NNReal) < death omega},
              f n (Y (Real.toNNReal t) omega) ∂P ∂volume :=
          iSup_congr fun n => ih n
      _ = ∫⁻ t in Set.Ici (0 : Real), ENNReal.ofReal (Real.exp (-q * t)) *
            ∫⁻ omega in {omega : Omega |
              (Real.toNNReal t : WithTop NNReal) < death omega},
              (fun x : Real => ⨆ n, f n x) (Y (Real.toNNReal t) omega) ∂P
            ∂volume := by
          have hpt : ∀ t : Real, ENNReal.ofReal (Real.exp (-q * t)) *
                ∫⁻ omega in {omega : Omega |
                  (Real.toNNReal t : WithTop NNReal) < death omega},
                  (fun x : Real => ⨆ n, f n x) (Y (Real.toNNReal t) omega) ∂P
              = ⨆ n, ENNReal.ofReal (Real.exp (-q * t)) *
                ∫⁻ omega in {omega : Omega |
                  (Real.toNNReal t : WithTop NNReal) < death omega},
                  f n (Y (Real.toNNReal t) omega) ∂P := by
            intro t
            rw [hinner_iSup t, ENNReal.mul_iSup]
          have hinner_mono : ∀ (t : Real) ⦃n m : ℕ⦄, n ≤ m →
              (∫⁻ omega in {omega : Omega |
                  (Real.toNNReal t : WithTop NNReal) < death omega},
                f n (Y (Real.toNNReal t) omega) ∂P)
              ≤ (∫⁻ omega in {omega : Omega |
                  (Real.toNNReal t : WithTop NNReal) < death omega},
                f m (Y (Real.toNNReal t) omega) ∂P) :=
            fun t _ _ hnm => MeasureTheory.lintegral_mono_ae
              (Filter.Eventually.of_forall fun omega => hmono hnm _)
          rw [MeasureTheory.lintegral_congr hpt]
          refine (MeasureTheory.lintegral_iSup'
            (fun n => houterAE (f n) (hf n)) ?_).symm
          filter_upwards with t n m hnm
          dsimp only
          exact mul_le_mul_right (hinner_mono t hnm) _
