-- Prove2me | solution 1 for OAI.ShortDraftCusp.cusp19_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:05:53.271797+00:00
-- url     : https://prove2.me/submissions/81ae1c62-a1cb-4069-ba67-fd4a83588513

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ShortDraftCusp_upper_inversion_lower

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
open OAI.ShortDraftCusp
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCusp
theorem _root_.solution (ω : R) (hω : ω ^ 2 + ω + 1 = 0) :
    U ω * E * L (-(ω ^ 2)) = !![-1,-1;1,0] := by
  rw [upper_inversion_lower]
  have hw : ω + ω ^ 2 = -1 := by linear_combination hω
  rw [hw]
end OAI.ShortDraftCusp
