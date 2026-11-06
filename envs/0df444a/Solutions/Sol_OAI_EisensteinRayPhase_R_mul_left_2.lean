-- Prove2me | solution 2 for OAI.EisensteinRayPhase.R_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:07:00.743319+00:00
-- url     : https://prove2.me/submissions/7aad5828-58b2-43bd-b1ee-c15637f8196d

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
open OAI.EisensteinRayPhase

theorem solution (a b c : SquareClass) : R (a + b) c = R a c * R b c := by
  decide +revert
