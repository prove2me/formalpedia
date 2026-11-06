-- Prove2me | solution 1 for OAI.ConcreteBreveE.normalizedTraceGaussProduct_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:44.076467+00:00
-- url     : https://prove2.me/submissions/5a267593-e2c9-4476-9b84-fef329d32aeb

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Theorems.Thm_OAI_ConcreteBreveE_gauss_sum_breveE_actual_O
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_product
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span


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
open OAI.ConcreteBreveE
open EisensteinEmbedding ConcreteTraceCRT
namespace OAI.ConcreteBreveE
theorem _root_.solution
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b}))
    (χa : MulChar (O ⧸ Ideal.span {a}) ℂ)
    (χb : MulChar (O ⧸ Ideal.span {b}) ℂ) :
    normalizedTraceGaussProduct a b ha hb χa χb =
      χa (Ideal.Quotient.mk (Ideal.span {a}) b) *
      χb (Ideal.Quotient.mk (Ideal.span {b}) a) *
      normalizedTraceGauss a ha χa * normalizedTraceGauss b hb χb := by
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {b}) := finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  have hsum := gauss_sum_breveE_actual_O a b ha hb hcop χa χb
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) =
      (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul]
    norm_cast
  change (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    χa (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    χb (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates a b ha hb x) /
      (‖eisEmbedding (a * b)‖ : ℂ) = _
  rw [hsum, hnorm]
  unfold normalizedTraceGauss
  ring
end OAI.ConcreteBreveE
