-- Prove2me | solution 1 for OAI.EisensteinEPrimaryPhase.bits_squareclass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:54.682342+00:00
-- url     : https://prove2.me/submissions/99c2ef80-4c0e-4668-9e8f-20d55dbeb7ca

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
theorem _root_.solution (e f : Bit) (u : Coord) (hu : odd u) :
    bits (mul (rep e f) (mul u u)) = (e, f) := by
  decide +revert
end OAI.EisensteinEPrimaryPhase
