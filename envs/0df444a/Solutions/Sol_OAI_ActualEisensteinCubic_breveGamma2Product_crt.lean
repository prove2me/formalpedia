-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.breveGamma2Product_crt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:12:43.473218+00:00
-- url     : https://prove2.me/submissions/e1b95cb8-0ed3-4c00-9b87-ec7b3386fbf4

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Theorems.Thm_OAI_ConcreteBreveE_gauss_sum_breveE_actual_O
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_product
import Theorems.Thm_OAI_ConcreteTraceCRT_finite_quotient_span
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
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    [haMax : (Ideal.span {a}).IsMaximal]
    [hbMax : (Ideal.span {b}).IsMaximal]
    (hgooda : lambda ∉ Ideal.span {a})
    (hgoodb : lambda ∉ Ideal.span {b})
    (hcop : IsCoprime (Ideal.span {a}) (Ideal.span {b})) :
    breveGamma2Product a b ha hb hgooda hgoodb =
      (canonicalSextic (Ideal.span {a}) hgooda
        (Ideal.Quotient.mk (Ideal.span {a}) b)) ^ 2 *
      (canonicalSextic (Ideal.span {b}) hgoodb
        (Ideal.Quotient.mk (Ideal.span {b}) a)) ^ 2 *
      breveGamma2 (Ideal.span {a}) hgooda a rfl ha *
      breveGamma2 (Ideal.span {b}) hgoodb b rfl hb := by
  let : Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) :=
    finite_quotient_product ha hb
  let : Fintype (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {a}) := finite_quotient_span ha
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  let : Finite (O ⧸ Ideal.span {b}) := finite_quotient_span hb
  let : Fintype (O ⧸ Ideal.span {b}) := Fintype.ofFinite _
  let χa := canonicalSextic (Ideal.span {a}) hgooda
  let χb := canonicalSextic (Ideal.span {b}) hgoodb
  have hsum := gauss_sum_breveE_actual_O a b ha hb hcop (χa ^ 2) (χb ^ 2)
  have hnorm : (‖eisEmbedding (a * b)‖ : ℂ) =
      (‖eisEmbedding a‖ : ℂ) * (‖eisEmbedding b‖ : ℂ) := by
    rw [map_mul, norm_mul]
    norm_cast
  change (∑ x : O ⧸ (Ideal.span {a}) * (Ideal.span {b}),
    (χa ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_left : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {a}) x) *
    (χb ^ 2) (Ideal.Quotient.factor
      (Ideal.mul_le_right : (Ideal.span {a}) * (Ideal.span {b}) ≤ Ideal.span {b}) x) *
    eisTraceProdChar ShortDraftTrace.breveE breveE_period_coordinates a b ha hb x) /
      (‖eisEmbedding (a * b)‖ : ℂ) = _
  rw [hsum, hnorm]
  simp only [χa.pow_apply' (by decide : (2 : ℕ) ≠ 0),
    χb.pow_apply' (by decide : (2 : ℕ) ≠ 0)]
  unfold breveGamma2
  ring
end OAI.ActualEisensteinCubic
