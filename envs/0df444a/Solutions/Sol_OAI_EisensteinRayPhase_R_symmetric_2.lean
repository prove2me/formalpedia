-- Prove2me | solution 2 for OAI.EisensteinRayPhase.R_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:17.297948+00:00
-- url     : https://prove2.me/submissions/5a3d65f0-ce2a-4427-b4dc-ad8274566cfe

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
theorem _root_.solution (a b : SquareClass) : R a b = R b a := by
  decide +revert
end OAI.EisensteinRayPhase
