-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.residue_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:36:34.040962+00:00
-- url     : https://prove2.me/submissions/682898a3-1c0c-47fa-bb7e-a24c9b62c1cd

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_mul

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
theorem _root_.solution (x : O) :
    residue (x^2) = EisensteinEPrimaryPhase.mul (residue x) (residue x) := by
  simpa [pow_two] using residue_mul x x
end OAI.ActualEisensteinCoordinates
