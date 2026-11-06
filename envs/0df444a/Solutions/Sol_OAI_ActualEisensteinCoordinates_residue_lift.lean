-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.residue_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:30.817022+00:00
-- url     : https://prove2.me/submissions/98920c17-c7f3-476d-8db3-a16d071d39f9

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_eval

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
open OAI.ActualEisensteinCoordinates
namespace OAI.ActualEisensteinCoordinates
theorem _root_.solution (v : EisensteinEPrimaryPhase.Coord) :
    residue (lift v) = v := by
  simp [lift, residue_eval]
end OAI.ActualEisensteinCoordinates
