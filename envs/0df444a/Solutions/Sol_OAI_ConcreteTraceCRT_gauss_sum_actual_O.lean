-- Prove2me | solution 1 for OAI.ConcreteTraceCRT.gauss_sum_actual_O
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:39:57.109934+00:00
-- url     : https://prove2.me/submissions/b3b81316-ac74-4a10-ae43-4c7248a4a2c2

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_IdealGaussCRT_gauss_sum_trace_crt_of_coprime
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
open OAI.ConcreteTraceCRT
open EisensteinEmbedding IdealGaussCRT
namespace OAI.ConcreteTraceCRT
theorem _root_.solution
    (ψ : AddChar ℂ ℂ)
    (hperiod : ∀ c d : ℤ,
      ψ (((c : ℂ) + (d : ℂ) * omega3) / eisLam) = 1)
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    [Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b}))]
    [Fintype (O ⧸ Ideal.span {a})]
    [Fintype (O ⧸ Ideal.span {b})]
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
      χa (Ideal.Quotient.factor
        (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
      χb (Ideal.Quotient.factor
        (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
      eisTraceProdChar ψ hperiod a b ha hb x) =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      gaussSum χa (eisTraceModChar ψ hperiod a ha) *
      gaussSum χb (eisTraceModChar ψ hperiod b hb) := by
  simpa only [eisTraceProdChar, eisTraceModChar] using
    gauss_sum_trace_crt_of_coprime eisEmbedding ψ eisLam a b hcop
      (eisEmbedding_ne_zero ha) (eisEmbedding_ne_zero hb)
      eisLam_ne_zero (eisPeriod ψ hperiod) χa χb
end OAI.ConcreteTraceCRT
