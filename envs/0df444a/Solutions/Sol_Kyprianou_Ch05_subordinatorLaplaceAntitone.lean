-- Prove2me | solution 1 for Kyprianou.Ch05.subordinatorLaplaceAntitone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:16:24.579711+00:00
-- url     : https://prove2.me/submissions/0eea4038-9f08-45fa-807d-af82ecf63800

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_indepFun_increment
import Theorems.Thm_ProbabilityTheory_IsLevyProcess_identDistrib_increment
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05


/-- Monotone sample paths imply antitonicity of the Laplace transform. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : NNReal → Omega → Real)
    (hY : Kyprianou.Ch03.IsSubordinator P Y)
    (theta : Real) (htheta : 0 < theta) :
    Antitone (fun t : NNReal => (∫⁻ w, ENNReal.ofReal (Real.exp (-theta * Y t w)) ∂P)) := by
  intro s t hst
  apply lintegral_mono_ae
  filter_upwards [hY.2] with w hw
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (hw hst) (neg_nonpos.mpr htheta.le)
