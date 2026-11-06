-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.residue_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:30.252549+00:00
-- url     : https://prove2.me/submissions/05adb8c1-0d70-4d1d-a6d6-d3eafb08c9b9

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_mul
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords
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
theorem _root_.solution (x y : O) :
    residue (x*y) = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
  calc
    residue (x*y) = residue (eval (coords x).1 (coords x).2 *
        eval (coords y).1 (coords y).2) := by rw [eval_coords, eval_coords]
    _ = EisensteinEPrimaryPhase.mul (residue x) (residue y) := by
      rw [eval_mul, residue_eval]
      simp [residue, EisensteinEPrimaryPhase.mul]
end OAI.ActualEisensteinCoordinates
