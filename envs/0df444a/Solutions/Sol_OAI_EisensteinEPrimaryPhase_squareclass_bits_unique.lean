-- Prove2me | solution 1 for OAI.EisensteinEPrimaryPhase.squareclass_bits_unique
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:44.322943+00:00
-- url     : https://prove2.me/submissions/d27a73e2-ed0e-4846-bbb6-db201659dfbf

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
theorem _root_.solution (e f e' f' : Bit) (u v : Coord)
    (hu : odd u) (hv : odd v)
    (h : mul (rep e f) (mul u u) = mul (rep e' f') (mul v v)) :
    e = e' ∧ f = f' := by
  decide +revert
end OAI.EisensteinEPrimaryPhase
