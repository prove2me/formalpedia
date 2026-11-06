-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.norm_squareclass_actual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:09.784891+00:00
-- url     : https://prove2.me/submissions/6a9c6f33-45b2-468f-9fe5-a3abd5044844

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_EisensteinEPrimaryPhase_norm_squareclass
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_mul
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_pow_two
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_lift

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinCoordinates
namespace OAI.ActualEisensteinCoordinates
theorem _root_.solution
    (e f : EisensteinEPrimaryPhase.Bit) (u : O)
    (hu : EisensteinEPrimaryPhase.odd (residue u)) :
    EisensteinEPrimaryPhase.norm
      (residue (lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2)) =
      (if f = 0 then 1 else 3) := by
  rw [residue_mul, residue_pow_two, residue_lift]
  exact EisensteinEPrimaryPhase.norm_squareclass e f (residue u) hu
end OAI.ActualEisensteinCoordinates
