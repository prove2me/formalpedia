-- Prove2me | solution 1 for OAI.PrimitiveTrace.eisTraceModChar_breveE_primitive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:43.693064+00:00
-- url     : https://prove2.me/submissions/05af82ac-c742-4d1a-bcbf-a22f874ead00

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_ne_one

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
open OAI.PrimitiveTrace
open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT
namespace OAI.PrimitiveTrace
theorem _root_.solution
    (P : Ideal O) [P.IsMaximal] (p : O)
    (hP : P = Ideal.span {p}) (hp : p ≠ 0) :
    (eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp).IsPrimitive := by
  have : (Ideal.span {p}).IsMaximal := hP ▸ inferInstance
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  exact AddChar.IsPrimitive.of_ne_one
    (eisTraceModChar_breveE_ne_one P p hP hp)
end OAI.PrimitiveTrace
