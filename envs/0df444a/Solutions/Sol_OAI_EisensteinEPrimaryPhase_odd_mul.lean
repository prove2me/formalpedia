-- Prove2me | solution 1 for OAI.EisensteinEPrimaryPhase.odd_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:55.322406+00:00
-- url     : https://prove2.me/submissions/d79791f7-babd-4c6e-8a45-07cbb3d91def

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
theorem _root_.solution (x y : Coord) (hx : odd x) (hy : odd y) : odd (mul x y) := by
  decide +revert
end OAI.EisensteinEPrimaryPhase
