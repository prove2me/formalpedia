-- Prove2me | solution 1 for OAI.EisensteinRayPhase.R_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:06:02.440726+00:00
-- url     : https://prove2.me/submissions/641b0c6c-3ce6-48e7-8d35-28e33567ce0d

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

theorem solution (a b : SquareClass) : R a b = R b a := by
  unfold R
  congr 1
  ring
