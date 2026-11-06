-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.residue_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:34:32.322587+00:00
-- url     : https://prove2.me/submissions/94d9a195-d8f9-43cb-81c2-0bd1c4f41819

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ActualEisensteinCoordinates_unique_coordinates
import Theorems.Thm_OAI_ActualEisensteinCoordinates_eval_coords

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
theorem _root_.solution (a b : ℤ) :
    residue (eval a b) = ((a : ZMod 4), (b : ZMod 4)) := by
  have h := unique_coordinates (eval_coords (eval a b))
  exact Prod.ext (congrArg (fun n : ℤ => (n : ZMod 4)) h.1)
    (congrArg (fun n : ℤ => (n : ZMod 4)) h.2)
end OAI.ActualEisensteinCoordinates
