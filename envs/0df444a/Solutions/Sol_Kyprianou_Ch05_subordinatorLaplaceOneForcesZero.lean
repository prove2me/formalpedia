-- Prove2me | solution 1 for Kyprianou.Ch05.subordinatorLaplaceOneForcesZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:17:15.336422+00:00
-- url     : https://prove2.me/submissions/84cc1fa8-3b4e-42ee-9122-28eef5e6b30b

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- At a positive Laplace argument, a nonnegative subordinator marginal with Laplace transform one must be zero almost surely. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) (t : NNReal)
    (hunit : (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) = 1) :
    ∀ᵐ w ∂P, Y t w = 0 := by
  let f : Omega → ENNReal := fun w => ENNReal.ofReal (Real.exp (-theta * Y t w))
  have hf : AEMeasurable f P :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul _))).comp_aemeasurable
      (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hY.1 t)
  have hn : ∀ᵐ w ∂P, 0 ≤ Y t w := by
    filter_upwards [hY.2] with w hw
    simpa [hY.1.start_zero] using hw (show (0 : NNReal) ≤ t from bot_le)
  have hb : ∀ᵐ w ∂P, f w ≤ 1 := by
    filter_upwards [hn] with w hw
    change ENNReal.ofReal (Real.exp (-theta * Y t w)) ≤ 1
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.exp_le_one_iff]
    nlinarith
  have hdef : AEMeasurable (fun w => 1 - f w) P := aemeasurable_const.sub hf
  have hsum : (∫⁻ w, 1 - f w ∂P) + ∫⁻ w, f w ∂P = 1 := by
    rw [← lintegral_add_left' hdef]
    calc
      _ = ∫⁻ _w : Omega, (1 : ENNReal) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hb] with w hw
        exact tsub_add_cancel_of_le hw
      _ = 1 := by simp
  change (∫⁻ w, f w ∂P) = 1 at hunit
  rw [hunit] at hsum
  have hd : (∫⁻ w, 1 - f w ∂P) = 0 := by
    have h' : (∫⁻ w, 1 - f w ∂P) + 1 = 0 + 1 := by simpa using hsum
    have ht := congrArg ENNReal.toReal h'
    have hfin : (∫⁻ w, 1 - f w ∂P) ≠ ⊤ := by
      intro htop
      rw [htop] at hsum
      simp at hsum
    rw [ENNReal.toReal_add hfin ENNReal.one_ne_top,
      ENNReal.toReal_add ENNReal.zero_ne_top ENNReal.one_ne_top] at ht
    simp at ht
    have hzero : (∫⁻ w, 1 - f w ∂P).toReal = 0 := by linarith
    simpa [hzero] using (ENNReal.ofReal_toReal hfin).symm
  have hae := (lintegral_eq_zero_iff' hdef).mp hd
  filter_upwards [hae, hb] with w hw hw'
  have hf1 : f w = 1 := le_antisymm hw' (tsub_eq_zero_iff_le.mp hw)
  have hr := congrArg ENNReal.toReal hf1
  simp only [f, ENNReal.toReal_ofReal (Real.exp_nonneg _), ENNReal.toReal_one] at hr
  have harg : -theta * Y t w = 0 :=
    Real.exp_injective (hr.trans Real.exp_zero.symm)
  nlinarith
