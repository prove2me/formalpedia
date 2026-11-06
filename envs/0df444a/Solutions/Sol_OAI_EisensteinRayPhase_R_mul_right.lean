-- Prove2me | solution 1 for OAI.EisensteinRayPhase.R_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:21.429879+00:00
-- url     : https://prove2.me/submissions/9050608b-e864-493f-89ac-cc4e72970f8d

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
namespace OAI.EisensteinRayPhase
theorem _root_.solution (a b c : SquareClass) : R a (b + c) = R a b * R a c := by
  decide +revert
end OAI.EisensteinRayPhase
