-- Prove2me | solution 1 for OAI.ShortDraftCusp.principal_case_ramified
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:06:13.287826+00:00
-- url     : https://prove2.me/submissions/b85d7d52-6379-478f-acee-e8b4b34cd191

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
    (ha : a = 1) (hb : b = 0) (hc : c = u) :
    (!![a - u * b,b;c - u * d,d] : Matrix (Fin 2) (Fin 2) R) = 1 := by
  subst a
  subst b
  subst c
  have hd : d = 1 := by simpa using hdet
  subst d
  simp [Matrix.one_fin_two]
end OAI.ShortDraftCusp
