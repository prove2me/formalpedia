-- Prove2me | solution 1 for OAI.EisensteinEPrimaryPhase.ePrimary_squareclass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:33:29.050437+00:00
-- url     : https://prove2.me/submissions/e72e927e-42d8-4a9a-9720-81adedaaa25e

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
    ePrimary (mul (rep e f) (mul u u)) ↔ e = 0 := by
  decide +revert
end OAI.EisensteinEPrimaryPhase
