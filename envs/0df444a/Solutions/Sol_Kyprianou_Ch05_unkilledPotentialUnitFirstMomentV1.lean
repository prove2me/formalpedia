-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPotentialUnitFirstMomentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-27T00:11:17.16031+00:00
-- url     : https://prove2.me/submissions/0fd535ca-7352-4bf2-865f-7d627ecd2d09

import Theorems.Thm_Kyprianou_Ch05_unkilledPotentialMapV1
import Theorems.Thm_Kyprianou_Ch05_subordinatorMeanLinearV1
import Theorems.Thm_Kyprianou_Ch05_unitExponentialClockMeanV1
import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Tonelli gives the first moment of the unit-discount potential. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U)
    (hFiniteMean : Integrable (Y (1 : NNReal)) P) :
    (∫⁻ x : Real, ENNReal.ofReal x ∂(U 1)) =
      ENNReal.ofReal (∫ w, Y 1 w ∂P) := by
  obtain ⟨Z, hZ, he, hm⟩ := unkilledPotentialMapV1 P Y death hKilled U hPotential
  let m := ∫ w, Y 1 w ∂P
  have hnonneg (t : NNReal) : 0 ≤ᵐ[P] Y t := by
    filter_upwards [hKilled.1.2] with w hw
    simpa [hKilled.1.1.start_zero] using hw (bot_le : 0 ≤ t)
  have hl (t : Real) : (∫⁻ w, ENNReal.ofReal (Z (Real.toNNReal t) w) ∂P) =
      ENNReal.ofReal ((Real.toNNReal t : Real) * m) := by
    rw [lintegral_congr_ae (show (fun w => ENNReal.ofReal (Z (Real.toNNReal t) w)) =ᵐ[P]
      (fun w => ENNReal.ofReal (Y (Real.toNNReal t) w)) from by
        filter_upwards [he] with w hw using congrArg ENNReal.ofReal (hw _))]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (subordinatorMeanLinearV1 P Y hKilled.1 hFiniteMean _).1 (hnonneg _)]
    rw [(subordinatorMeanLinearV1 P Y hKilled.1 hFiniteMean _).2]
  have hmass : (∫⁻ x : Real, ENNReal.ofReal x ∂(U 1)) = ENNReal.ofReal m := by
    rw [hm 1 (by norm_num), lintegral_map ENNReal.measurable_ofReal hZ,
      lintegral_prod (fun p : Real × Omega => ENNReal.ofReal (Z (Real.toNNReal p.1) p.2))
        (ENNReal.measurable_ofReal.comp hZ).aemeasurable]
    simp_rw [hl]
    rw [lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
    calc
      _ = ∫⁻ t in Set.Ici (0 : Real),
          ENNReal.ofReal (Real.exp (-t) * t) * ENNReal.ofReal m ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        change ENNReal.ofReal (Real.exp (-1*t)) * ENNReal.ofReal ((Real.toNNReal t : Real)*m) =
          ENNReal.ofReal (Real.exp (-t)*t) * ENNReal.ofReal m
        rw [neg_mul, one_mul, Real.coe_toNNReal _ ht, ENNReal.ofReal_mul ht,
          ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc]
      _ = ENNReal.ofReal m := by
        rw [lintegral_mul_const _ (by fun_prop), unitExponentialClockMeanV1, one_mul]
  exact hmass
