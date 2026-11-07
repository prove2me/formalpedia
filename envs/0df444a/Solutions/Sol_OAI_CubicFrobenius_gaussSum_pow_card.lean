-- Prove2me | solution 1 for OAI.CubicFrobenius.gaussSum_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:11:06.036857+00:00
-- url     : https://prove2.me/submissions/5b22f3c9-8d66-4ec9-8adf-7d9643c41de1

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_ActiveGaussFactorization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicTrace
import Theorems.Thm_OAI_ActualEisensteinCubic_principalSexticRow_mk
import Theorems.Thm_OAI_EisensteinSchwartzPoisson_verticalSlice_apply
import Theorems.Thm_OAI_FiniteGaussPhase_productElementCRT_mk
import Theorems.Thm_OAI_IdealGaussCRT_quotientProdEquivPi_mk
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.ActualEisensteinCubic.principalSexticRow_mk
attribute [local simp] OAI.EisensteinSchwartzPoisson.verticalSlice_apply
attribute [local simp] OAI.FiniteGaussPhase.productElementCRT_mk
attribute [local simp] OAI.IdealGaussCRT.quotientProdEquivPi_mk
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
open OAI.CubicFrobenius
namespace OAI.CubicFrobenius
theorem _root_.solution (F F' E : Type*) [Field F] [Fintype F]
    [Field F'] [Fintype F'] [Field E] [Algebra F' E]
    (χ : MulChar F F') (ψ : AddChar F E) :
    gaussSum (χ.ringHomComp (algebraMap F' E)) ψ ^ Fintype.card F' =
      gaussSum (χ.ringHomComp (algebraMap F' E))
        (ψ.mulShift (Fintype.card F' : F)) := by
  obtain ⟨n, hp, hcard⟩ := FiniteField.card F' (ringChar F')
  have hchar := Algebra.ringChar_eq F' E
  have hpE : (ringChar E).Prime := hchar ▸ hp
  let : Fact (ringChar E).Prime := ⟨hpE⟩
  have hcardE : Fintype.card F' = ringChar E ^ (n : ℕ) := by simpa only [hchar] using hcard
  unfold gaussSum
  rw [hcardE, sum_pow_char_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [mul_pow, ← hcardE]
  change (algebraMap F' E (χ x)) ^ Fintype.card F' * ψ x ^ Fintype.card F' = _
  rw [← map_pow, FiniteField.pow_card, ← AddChar.mulShift_spec']
  rfl
end OAI.CubicFrobenius
