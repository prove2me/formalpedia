-- Prove2me | solution 1 for OAI.ActualEisensteinCoordinates.exists_squareclass_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:06.772273+00:00
-- url     : https://prove2.me/submissions/a3d234b5-d2b5-4ab6-9fd1-2e6598f30e86

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_EisensteinEPrimaryPhase_exists_squareclass
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_mul
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_pow_two
import Theorems.Thm_OAI_ActualEisensteinCoordinates_congr_mod_four_of_residue_eq
import Theorems.Thm_OAI_ActualEisensteinCoordinates_residue_lift

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
theorem _root_.solution (x : O)
    (hx : EisensteinEPrimaryPhase.odd (residue x)) :
    ∃ (e f : EisensteinEPrimaryPhase.Bit) (u z : O),
      x - lift (EisensteinEPrimaryPhase.rep e f) * u ^ 2 = 4 * z := by
  obtain ⟨e, f, v, hv, hclass⟩ :=
    EisensteinEPrimaryPhase.exists_squareclass (residue x) hx
  refine ⟨e, f, lift v, ?_⟩
  apply congr_mod_four_of_residue_eq
  rw [residue_mul, residue_pow_two, residue_lift, residue_lift]
  exact hclass
end OAI.ActualEisensteinCoordinates
