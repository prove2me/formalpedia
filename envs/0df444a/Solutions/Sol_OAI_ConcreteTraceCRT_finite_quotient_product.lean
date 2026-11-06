-- Prove2me | solution 1 for OAI.ConcreteTraceCRT.finite_quotient_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:15.614555+00:00
-- url     : https://prove2.me/submissions/5dd423aa-13a2-4b2f-a42b-50a7caff07ae

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
open OAI.ConcreteTraceCRT
open EisensteinEmbedding IdealGaussCRT
namespace OAI.ConcreteTraceCRT
theorem _root_.solution {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) :
    Finite (O ⧸ (Ideal.span {a}) * (Ideal.span {b})) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  have hab : a * b = 0 := Ideal.span_singleton_eq_bot.mp (by
    simpa only [Ideal.span_singleton_mul_span_singleton] using h)
  exact mul_ne_zero ha hb hab
end OAI.ConcreteTraceCRT
