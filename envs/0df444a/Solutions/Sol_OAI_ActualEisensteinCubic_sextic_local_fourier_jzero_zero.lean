-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sextic_local_fourier_jzero_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:26.823042+00:00
-- url     : https://prove2.me/submissions/65ca9a00-a536-4cfe-96a9-09ca2fc10d06

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
    (hgood : lambda ∉ P) (ψ : AddChar (O ⧸ P) ℂ) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ 0) y *
        ψ (-(0 : O ⧸ P) * y)) = (Nat.card (O ⧸ P) : ℂ) - 1 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hsum := MulChar.sum_one_eq_card_units (R := O ⧸ P) (R' := ℂ)
  have hcard : (Fintype.card (O ⧸ P) : ℂ) =
      (Fintype.card (O ⧸ P)ˣ : ℂ) + 1 := by
    exact_mod_cast (Fintype.card_eq_card_units_add_one (α := O ⧸ P))
  simpa only [pow_zero, neg_zero, zero_mul, map_zero_eq_one, mul_one,
    Nat.card_eq_fintype_card, hcard, add_sub_cancel_right] using hsum
end OAI.ActualEisensteinCubic
