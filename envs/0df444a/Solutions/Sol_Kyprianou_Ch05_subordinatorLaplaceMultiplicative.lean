-- Prove2me | solution 1 for Kyprianou.Ch05.subordinatorLaplaceMultiplicative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:16:34.210987+00:00
-- url     : https://prove2.me/submissions/3f68d913-5f31-4572-87d5-daf39ada7b95

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_identDistrib_increment
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05


/-- Stationary independent increments give multiplicativity of the Laplace transform. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) :
    ∀ s t : NNReal, (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y (s+t) w)) ∂P) =
      (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y s w)) ∂P) * (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P) := by
  let f : Real → ENNReal := fun x => ENNReal.ofReal (Real.exp (-theta * x))
  have hf : Measurable f :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const_mul _))
  have hm (t : NNReal) : AEMeasurable (fun w => f (Y t w)) P :=
    hf.comp_aemeasurable (Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P Y hY.1 t)
  intro s t
  let J := ProbabilityTheory.increment Y s (s+t)
  have hind := hY.1.indepFun_increment (show (0 : NNReal) ≤ s from bot_le)
    (show s ≤ s+t from le_add_of_nonneg_right bot_le)
  have hstat := hY.1.identDistrib_increment s t
  have hinc (r : NNReal) : ProbabilityTheory.increment Y 0 r = Y r := by
    funext w
    simp [ProbabilityTheory.increment, hY.1.start_zero]
  rw [hinc s] at hind
  rw [hinc t] at hstat
  have hJ : AEMeasurable (fun w => f (J w)) P :=
    hf.comp_aemeasurable hstat.1
  have hprod := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun''
    (hm s) hJ (hind.comp hf hf)
  have hdist : (∫⁻ w, f (J w) ∂P) = ∫⁻ w, f (Y t w) ∂P :=
    (hstat.comp hf).lintegral_eq
  have he (w : Omega) : f (Y (s+t) w) = f (Y s w) * f (J w) := by
    simp only [f, J, ProbabilityTheory.increment, ← ENNReal.ofReal_mul (Real.exp_nonneg _),
      ← Real.exp_add]
    congr 2
    ring
  change (∫⁻ w, f (Y (s+t) w) ∂P) = _
  simp_rw [he]
  rw [hprod, hdist]
