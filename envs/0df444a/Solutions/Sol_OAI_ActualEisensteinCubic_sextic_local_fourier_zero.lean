-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.sextic_local_fourier_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:24.33582+00:00
-- url     : https://prove2.me/submissions/4f3ca35e-b527-4a1a-9dcc-fb3da21cc3c9

import Definitions.Def_OAI_NumberTheory_DirichletL_ChineseRemainder_AdditiveCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ChineseRemainder
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Theorems.Thm_OAI_ActualEisensteinCubic_ringComplex_injective
import Theorems.Thm_OAI_ActualEisensteinCubic_sexticChar_order
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
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
namespace EisensteinEmbedding
end EisensteinEmbedding
namespace ConcreteTraceCRT
open EisensteinEmbedding IdealGaussCRT
end ConcreteTraceCRT
namespace ConcreteBreveE
open EisensteinEmbedding ConcreteTraceCRT
end ConcreteBreveE
namespace ActualEisensteinCubic
open AddChar MulChar
private theorem sextic_complex_pow_ne_one (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    ((sexticChar P hgood).ringHomComp ringComplex) ^ j ≠ 1 := by
  rw [MulChar.ringHomComp_pow]
  apply (MulChar.ringHomComp_ne_one_iff ringComplex_injective).2
  apply pow_ne_one_of_lt_orderOf hj0
  rwa [sexticChar_order P hgood hchar]
open AddChar MulChar
end ActualEisensteinCubic
namespace PrimitiveTrace
open Complex
open scoped ComplexConjugate
open EisensteinEmbedding ConcreteTraceCRT
end PrimitiveTrace
end
end OAI
end

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
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (ψ : AddChar (O ⧸ P) ℂ) (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) :
    (∑ y : O ⧸ P,
      (((sexticChar P hgood).ringHomComp ringComplex) ^ j) y * ψ (-(0 : O ⧸ P) * y)) =
    0 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let χ : MulChar (O ⧸ P) ℂ := ((sexticChar P hgood).ringHomComp ringComplex) ^ j
  have hχ : χ ≠ 1 := sextic_complex_pow_ne_one P hgood hchar hj0 hj6
  simpa only [χ, neg_zero, zero_mul, map_zero_eq_one, mul_one] using
    MulChar.sum_eq_zero_of_ne_one hχ
end OAI.ActualEisensteinCubic
