-- Prove2me | solution 1 for Kyprianou.Ch05.unkilledPotentialUnitProbability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:23:10.531865+00:00
-- url     : https://prove2.me/submissions/09bb0dc9-a960-41be-8b8e-ea9a555a1425

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RenewalMeasure
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_Kyprianou_Ch05_killedPotential_expNeg_setLintegral
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- The unit-discount potential of an unkilled subordinator has total mass one. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real) (death : Omega → WithTop NNReal)
    (hKilled : IsKilledSubordinator P Y death 0)
    (U : Real → Measure Real)
    (hPotential : IsKilledPotentialFamily P Y death U) :
    IsProbabilityMeasure (U 1) := by
  have hd := hKilled.2.2.2.1 rfl
  constructor
  rw [(hPotential 1 (by norm_num)).2 Set.univ MeasurableSet.univ]
  have he (t : Real) : {w : Omega |
      (Real.toNNReal t : WithTop NNReal) < death w ∧ Y (Real.toNNReal t) w ∈ Set.univ} =
      Set.univ := by
    ext w
    simp [hd w]
    first | exact WithTop.coe_lt_top _ | exact WithTop.coe_lt_top
  simp_rw [he, measure_univ, mul_one]
  rw [killedPotential_expNeg_setLintegral 1 (by norm_num)]
  norm_num
