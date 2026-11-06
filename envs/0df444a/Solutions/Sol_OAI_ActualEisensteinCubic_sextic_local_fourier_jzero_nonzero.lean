-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sextic_local_fourier_jzero_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:24.923184+00:00
-- url     : https://prove2.me/submissions/e690ed1b-4b38-4d61-84f2-0493805a6016

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
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
open AddChar MulChar
namespace OAI.ActualEisensteinCubic
theorem _root_.solution (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ)
    (hψ : ψ.IsPrimitive) (h : O ⧸ P) (hh : h ≠ 0) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ 0) y * ψ (-h * y)) =
      -1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hneg : -h ≠ 0 := neg_ne_zero.mpr hh
  have hnon : ψ.mulShift (-h) ≠ 1 := hψ hneg
  have ht := gaussSum_one_left hnon
  simpa only [pow_zero, gaussSum, AddChar.mulShift_apply] using ht
end OAI.ActualEisensteinCubic
