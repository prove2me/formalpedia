-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.canonicalSextic_pow_three_quadratic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:28.9838+00:00
-- url     : https://prove2.me/submissions/d57b54a0-fe33-4273-9765-52125a32a014

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_powers
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



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
open EisensteinEmbedding ConcreteTraceCRT PrimitiveTrace
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) :
    canonicalSextic P hgood ^ 3 =
      (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom ℂ) := by
  change ((sexticChar P hgood).ringHomComp eisEmbedding) ^ 3 = _
  rw [MulChar.ringHomComp_pow, (sexticChar_powers P hgood).2.1]
  ext x
  change eisEmbedding ((quadraticChar (O ⧸ P) x : ℤ) : O) =
    ((quadraticChar (O ⧸ P) x : ℤ) : ℂ)
  simp
end OAI.ActualEisensteinCubic
