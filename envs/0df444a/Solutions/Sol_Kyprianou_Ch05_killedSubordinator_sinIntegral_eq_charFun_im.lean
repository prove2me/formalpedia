-- Prove2me | solution 1 for Kyprianou.Ch05.killedSubordinator_sinIntegral_eq_charFun_im
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T11:30:14.521875+00:00
-- url     : https://prove2.me/submissions/5cdd7195-27cf-44ff-a984-1e23f44fc19c

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
    (∫ omega, Real.sin (u * Y t omega) ∂P) =
      (MeasureTheory.charFun (P.map (Y t)) u).im := by
  intro t u
  have hAe : AEMeasurable (Y t) P := by
    have hstat := hKilled.1.1.stationary_increments 0 t
    have hm2 : AEMeasurable (ProbabilityTheory.increment Y 0 t) P :=
      hstat.aemeasurable_snd
    have h0 : Y 0 = fun _ => (0 : Real) := hKilled.1.1.start_zero
    have heq : ProbabilityTheory.increment Y 0 t = Y t := by
      funext ω
      simp only [ProbabilityTheory.increment, h0]
      simp
    rwa [heq] at hm2
  haveI : IsFiniteMeasure (P.map (Y t)) := ⟨by
    rw [MeasureTheory.Measure.map_apply_of_aemeasurable hAe MeasurableSet.univ, Set.preimage_univ]
    exact measure_lt_top P Set.univ⟩
  have hInt : Integrable (fun z : Real => Complex.exp (u * z * Complex.I)) (P.map (Y t)) := by
    refine MeasureTheory.Integrable.of_bound ?_ 1 ?_
    · exact (by fun_prop : Continuous (fun z : Real => Complex.exp (u * z * Complex.I))).aestronglyMeasurable
    · filter_upwards with z
      simp only [← Complex.ofReal_mul, Complex.norm_exp_ofReal_mul_I, le_refl]
  have hsin : AEStronglyMeasurable (fun z : Real => Real.sin (u * z)) (P.map (Y t)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  calc (∫ omega, Real.sin (u * Y t omega) ∂P)
      = ∫ z, Real.sin (u * z) ∂(P.map (Y t)) :=
        (MeasureTheory.integral_map hAe hsin).symm
    _ = ∫ z, (Complex.exp (u * z * Complex.I)).im ∂(P.map (Y t)) := by
        apply integral_congr_ae
        filter_upwards with z
        simp only [← Complex.ofReal_mul, Complex.exp_ofReal_mul_I_im]
    _ = (∫ z, Complex.exp (u * z * Complex.I) ∂(P.map (Y t))).im :=
        integral_im hInt
    _ = (MeasureTheory.charFun (P.map (Y t)) u).im := by
        rw [MeasureTheory.charFun_apply_real]
