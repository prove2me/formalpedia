-- Prove2me | solution 1 for Kyprianou.Ch05.subordinatorLaplacePositiveBound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:17:54.99359+00:00
-- url     : https://prove2.me/submissions/600cfb24-db69-4211-a891-37a1f4bd67e8

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_identDistrib_increment
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05


/-- A nonnegative marginal has strictly positive exponential transform bounded by one. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) :
    ∀ t : NNReal, 0 < (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) ∧ (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) ≤ 1 := by
  let f : Real → ENNReal := fun x => ENNReal.ofReal (Real.exp (-theta * x))
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul _))
  have hm (t : NNReal) : AEMeasurable (fun w => f (Y t w)) P :=
    hf.comp_aemeasurable (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hY.1 t)
  have hn (t : NNReal) : ∀ᵐ w ∂P, 0 ≤ Y t w := by
    filter_upwards [hY.2] with w hw
    simpa [hY.1.start_zero] using hw (show (0 : NNReal) ≤ t from bot_le)
  have hbound (t : NNReal) : ∀ᵐ w ∂P, f (Y t w) ≤ 1 := by
    filter_upwards [hn t] with w hw
    change ENNReal.ofReal (Real.exp (-theta * Y t w)) ≤ 1
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_one_iff]
    nlinarith
  intro t
  change 0 < (∫⁻ w, f (Y t w) ∂P) ∧ (∫⁻ w, f (Y t w) ∂P) ≤ 1
  constructor
  · apply pos_iff_ne_zero.mpr
    intro hz
    have hzero := (lintegral_eq_zero_iff' (hm t)).mp hz
    have hfalse : ∀ᵐ w ∂P, False := by
      filter_upwards [hzero] with w hw
      have hp : 0 < f (Y t w) := ENNReal.ofReal_pos.mpr (Real.exp_pos _)
      exact (ne_of_gt hp) hw
    have hp : P = 0 := by simpa using hfalse
    have hc := congrArg (fun m : Measure Omega => m Set.univ) hp
    simpa using hc
  · calc
      _ ≤ ∫⁻ _w : Omega, (1 : ENNReal) ∂P := lintegral_mono_ae (hbound t)
      _ = 1 := by simp
