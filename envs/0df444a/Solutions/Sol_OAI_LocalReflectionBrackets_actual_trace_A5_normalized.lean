-- Prove2me | solution 1 for OAI.LocalReflectionBrackets.actual_trace_A5_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:19:27.73654+00:00
-- url     : https://prove2.me/submissions/d5a63965-7f0c-4129-9458-302a61fc51e1

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_GeneralPrimitiveTrace_eisTraceModChar_breveE_primitive
import Theorems.Thm_OAI_LocalReflectionBrackets_canonical_A5_normalized
import Theorems.Thm_OAI_PrimitiveTrace_eisTraceModChar_breveE_primitive


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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open OAI.LocalReflectionBrackets
open scoped Classical BigOperators
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]
open ActualEisensteinCubic
attribute [local instance] OAI.LocalReflectionBrackets.quotientFieldBounds
attribute [local instance] OAI.LocalReflectionBrackets.quotientFintypeBounds
namespace OAI.LocalReflectionBrackets
theorem _root_.solution (p : O) (hp : p ≠ 0) [(Ideal.span {p}).IsMaximal]
    (hgood : lambda ∉ Ideal.span {p}) (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (j : ℕ) (hj6 : j < 6) (σ ε : (O ⧸ Ideal.span {p})ˣ) (x : O ⧸ Ideal.span {p}) :
    let χ := canonicalSextic (Ideal.span {p}) hgood
    let ψ := ConcreteTraceCRT.eisTraceModChar ShortDraftTrace.breveE
      ConcreteBreveE.breveE_period_coordinates p hp
    activeRow χ ψ j σ ε x = ((χ⁻¹) ^ 2) σ * phase χ ψ j ε * bracket χ j x := by
  exact canonical_A5_normalized (Ideal.span {p}) hgood hchar _
    (PrimitiveTrace.eisTraceModChar_breveE_primitive (Ideal.span {p}) p rfl hp) j hj6 σ ε x
end OAI.LocalReflectionBrackets
