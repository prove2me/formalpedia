-- Prove2me | solution 1 for OAI.LocalReflectionBrackets.zeroFourierCoefficient_zero_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:21:00.842785+00:00
-- url     : https://prove2.me/submissions/81fb3602-1450-4759-8364-d6a082b5da4a

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_ReflectionBrackets
import Theorems.Thm_OAI_LocalReflectionBrackets_zeroFourierCoefficient_zero

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
namespace OAI.LocalReflectionBrackets
theorem _root_.solution (χ : MulChar F ℂ) :
    ‖zeroFourierCoefficient χ 0‖ ≤ 1 := by
  rw [zeroFourierCoefficient_zero]
  have hq : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hqpos : (0 : ℝ) < Fintype.card F := lt_of_lt_of_le zero_lt_one hq
  have hinv : (Fintype.card F : ℝ)⁻¹ ≤ 1 := by
    apply (inv_le_one₀ hqpos).mpr
    exact hq
  have hnonneg : 0 ≤ 1 - (Fintype.card F : ℝ)⁻¹ := sub_nonneg.mpr hinv
  have heq : (1 : ℂ) - (Fintype.card F : ℂ)⁻¹ = ((1 - (Fintype.card F : ℝ)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [heq, Complex.norm_real, Real.norm_of_nonneg hnonneg]
  exact sub_le_self _ (inv_nonneg.mpr hqpos.le)
end OAI.LocalReflectionBrackets
