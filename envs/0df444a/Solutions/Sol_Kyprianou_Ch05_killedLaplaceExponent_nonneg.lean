-- Prove2me | solution 1 for Kyprianou.Ch05.killedLaplaceExponent_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-26T03:26:45.310017+00:00
-- url     : https://prove2.me/submissions/fc9305ea-5950-489f-9a43-68c3bd52074b

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
    (eta d : Real) (Pi : Measure Real) (Phi : Real → Real)
    (hTriplet : Kyprianou.Ch05.IsKilledLaplaceTriplet eta d Pi Phi) :
    ∀ theta : Real, 0 ≤ theta → 0 ≤ Phi theta := by
  intro theta htheta
  obtain ⟨heta, hd, -, -, hPhi⟩ := hTriplet
  rw [hPhi theta htheta]
  refine add_nonneg (add_nonneg heta (mul_nonneg hd htheta)) ?_
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := hx
  have : Real.exp (-theta * x) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by rw [neg_mul]; exact neg_nonpos.mpr (mul_nonneg htheta hx0.le))
  exact sub_nonneg.mpr this
