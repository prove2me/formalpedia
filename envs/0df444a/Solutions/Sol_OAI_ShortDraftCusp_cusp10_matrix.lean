-- Prove2me | solution 1 for OAI.ShortDraftCusp.cusp10_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:03.631764+00:00
-- url     : https://prove2.me/submissions/3fa94170-d0eb-406f-8040-a728ffe534ec

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
theorem _root_.solution (ω : R) :
    U (-ω) * E * L (-ω) = E := by
  rw [upper_inversion_lower]
  simp [E]
end OAI.ShortDraftCusp
