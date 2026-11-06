-- Prove2me | solution 1 for OAI.EisensteinRayPhase.R_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:24.840714+00:00
-- url     : https://prove2.me/submissions/0db91440-9a72-4c38-8be3-6ff0e4ff235a

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
theorem _root_.solution (a : SquareClass) : R a a = (-1) ^ (a.2.val) := by
  decide +revert
end OAI.EisensteinRayPhase
