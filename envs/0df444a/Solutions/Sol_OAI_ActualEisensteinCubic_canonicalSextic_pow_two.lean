-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonicalSextic_pow_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:10:43.945781+00:00
-- url     : https://prove2.me/submissions/afae1aa6-7ce7-4397-8550-cf5851ef8e2c

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_powers


set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 2 =
      (cubicChar P hgood).ringHomComp eisEmbedding := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 2 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).1]
end OAI.ActualEisensteinCubic
