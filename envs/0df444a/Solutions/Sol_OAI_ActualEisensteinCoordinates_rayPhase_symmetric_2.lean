-- Prove2me | solution 2 for OAI.ActualEisensteinCoordinates.rayPhase_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:10:41.546021+00:00
-- url     : https://prove2.me/submissions/0b1da024-8612-4c69-9516-ccec07f84368

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
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

private theorem rayPhaseBits_symmetric_aux
    (a b : EisensteinEPrimaryPhase.Bit × EisensteinEPrimaryPhase.Bit) :
    rayPhaseBits a b = rayPhaseBits b a := by
  decide +revert

theorem solution (x y : O) : rayPhase x y = rayPhase y x :=
  rayPhaseBits_symmetric_aux _ _
