-- Prove2me | solution 1 for OAI.EisensteinEPrimaryPhase.bits_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:35.056219+00:00
-- url     : https://prove2.me/submissions/d589658f-a65c-4639-87a4-dadff55da9a9

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
open OAI.EisensteinEPrimaryPhase
namespace OAI.EisensteinEPrimaryPhase
theorem _root_.solution (x y : Coord) (hx : odd x) (hy : odd y) :
    bits (mul x y) = bits x + bits y := by
  decide +revert
end OAI.EisensteinEPrimaryPhase
