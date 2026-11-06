-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.rayBits_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:33.311003+00:00
-- url     : https://prove2.me/submissions/871b0496-1c4f-43dd-8df0-f98a2d1b7499

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_EisensteinEPrimaryPhase_bits_mul
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_mul
import Theorems.Thm_OAI_ActualEisensteinCoordinates_odd_residue_iff_not_two_dvd

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
theorem _root_.solution (x y : O)
    (hx : ¬ (2 : O) ∣ x) (hy : ¬ (2 : O) ∣ y) :
    rayBits (x*y) = rayBits x + rayBits y := by
  unfold rayBits
  rw [residue_mul]
  exact EisensteinEPrimaryPhase.bits_mul _ _
    ((odd_residue_iff_not_two_dvd x).mpr hx)
    ((odd_residue_iff_not_two_dvd y).mpr hy)
end OAI.ActualEisensteinCoordinates
