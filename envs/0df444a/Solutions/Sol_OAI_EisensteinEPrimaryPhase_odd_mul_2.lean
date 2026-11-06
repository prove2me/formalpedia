-- Prove2me | solution 2 for OAI.EisensteinEPrimaryPhase.odd_mul
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:08:54.86005+00:00
-- url     : https://prove2.me/submissions/3cd8a8f5-313d-40fa-ae74-701465c5898d

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

theorem solution (x y : Coord) (hx : odd x) (hy : odd y) : odd (mul x y) := by
  revert x y
  decide
