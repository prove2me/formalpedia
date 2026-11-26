-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_cosIntegral_eq_charFun_re
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T11:31:29.335736+00:00
-- url     : https://prove2.me/submissions/b46ec602-ccb6-4f91-98b2-db71e4e08ac6

import Mathlib
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_Kyprianou_Ch03_IsSubordinator
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
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
  ∀ (t : NNReal) (u : Real),
    (∫ omega, Real.cos (u * Y t omega) ∂P) =
        (MeasureTheory.charFun (P.map (Y t)) u).re := by
  intro t u
  have hstart : ∀ ω, Y 0 ω = 0 := fun ω => congrFun hKilled.1.1.start_zero ω
  have hAEM : AEMeasurable (Y t) P := by
    have h := (hKilled.1.1.stationary_increments 0 t).aemeasurable_snd
    have h' : AEMeasurable (fun ω => Y t ω - Y 0 ω) P := h
    have hfun : (fun ω => Y t ω - Y 0 ω) = Y t := by
      funext ω
      rw [hstart ω, sub_zero]
    exact hfun ▸ h'
  haveI : IsFiniteMeasure (P.map (Y t)) := MeasureTheory.Measure.isFiniteMeasure_map P (Y t)
  have hAESM : AEStronglyMeasurable
      (fun x : Real => Complex.exp (((u * x : Real) : ℂ) * Complex.I)) (P.map (Y t)) := by
    apply Continuous.aestronglyMeasurable
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul continuous_const)
  have hInt : Integrable
      (fun x : Real => Complex.exp (((u * x : Real) : ℂ) * Complex.I)) (P.map (Y t)) := by
    refine Integrable.of_bound hAESM 1 ?_
    filter_upwards with x
    rw [Complex.norm_exp_ofReal_mul_I]
  have hg : AEStronglyMeasurable (fun x : Real => Real.cos (u * x)) (P.map (Y t)) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  calc (∫ omega, Real.cos (u * Y t omega) ∂P)
      = ∫ x : Real, Real.cos (u * x) ∂(P.map (Y t)) := by
        rw [integral_map hAEM hg]
    _ = ∫ x : Real, (Complex.exp (((u * x : Real) : ℂ) * Complex.I)).re ∂(P.map (Y t)) := by
        apply integral_congr_ae
        filter_upwards with x
        rw [Complex.exp_ofReal_mul_I_re]
    _ = (∫ x : Real, Complex.exp (((u * x : Real) : ℂ) * Complex.I) ∂(P.map (Y t))).re := by
        exact integral_re hInt
    _ = (MeasureTheory.charFun (P.map (Y t)) u).re := by
        congr 1
