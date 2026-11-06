-- Prove2me | solution 1 for OAI.ConcreteTraceCRT.finite_quotient_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:12.526827+00:00
-- url     : https://prove2.me/submissions/63701f43-02af-41a5-ad50-635199bcc7fe

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding

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
theorem _root_.solution {a : O} (ha : a ≠ 0) :
    Finite (O ⧸ Ideal.span {a}) := by
  apply Ring.HasFiniteQuotients.finiteQuotient
  intro h
  exact ha (Ideal.span_singleton_eq_bot.mp h)
end OAI.ConcreteTraceCRT
