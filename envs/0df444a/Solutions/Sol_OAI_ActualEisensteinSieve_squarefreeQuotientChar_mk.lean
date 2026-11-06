-- Prove2me | solution 1 for OAI.ActualEisensteinSieve.squarefreeQuotientChar_mk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:51:12.234804+00:00
-- url     : https://prove2.me/submissions/b50bf739-570c-4094-b6c5-b329b706c6b0

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
section
namespace OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
namespace ActualEisensteinSieve
example (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
example (P : Ideal O) [P.IsMaximal] : Finite (O ⧸ P) := inferInstance
private theorem squarefreeCRT_mk
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    (hpair : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    squarefreeCRT P hpair (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      fun i => Ideal.Quotient.mk (P i) x := by
  classical
  funext i
  simp only [squarefreeCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change (Ideal.quotientInfToPiQuotient P
    (Ideal.Quotient.mk (⨅ i, P i) x)) i = Ideal.Quotient.mk (P i) x
  rfl
end ActualEisensteinSieve
end
end OAI
end

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
noncomputable section
open OAI.ActualEisensteinSieve
namespace OAI.ActualEisensteinSieve
theorem _root_.solution
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    squarefreeQuotientChar P hpair
        (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      ∏ i : ι, localQuadratic (P i) x := by
  classical
  simp only [squarefreeQuotientChar, MulChar.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, squarefreeCRT_mk, squarefreePiChar]
  apply Finset.prod_congr rfl
  intro i _
  rfl
end OAI.ActualEisensteinSieve
