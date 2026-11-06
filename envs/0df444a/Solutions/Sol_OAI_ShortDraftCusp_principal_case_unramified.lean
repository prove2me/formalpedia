-- Prove2me | solution 1 for OAI.ShortDraftCusp.principal_case_unramified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:15.305834+00:00
-- url     : https://prove2.me/submissions/ac5bb006-5593-430f-bb30-16b6f625bcee

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
open OAI.ShortDraftCusp
variable {R : Type*} [CommRing R]
namespace OAI.ShortDraftCusp
theorem _root_.solution (a b c d u : R)
    (hdet : a * d - b * c = 1)
    (hc : c = 1) (hd : d = 0) (hu : u = a) :
    (!![-b,a + u * b;-d,c + u * d] : Matrix (Fin 2) (Fin 2) R) = 1 := by
  subst c
  subst d
  subst u
  have hb : b = -1 := by linear_combination -hdet
  subst b
  simp [Matrix.one_fin_two]
end OAI.ShortDraftCusp
