-- Prove2me | solution 1 for OAI.ShortDraftCusp.ramified_minus_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:05.154752+00:00
-- url     : https://prove2.me/submissions/94bfb2a9-0030-4b96-96ed-74fb9c24d216

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Theorems.Thm_OAI_ShortDraftCusp_lower_add

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
    L (-(1 + 2 * ω)) = L (-1 - 3 * ω) * L ω := by
  rw [lower_add]
  congr 1
  ring
end OAI.ShortDraftCusp
