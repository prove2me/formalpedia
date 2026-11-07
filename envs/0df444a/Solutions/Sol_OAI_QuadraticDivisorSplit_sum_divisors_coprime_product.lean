-- Prove2me | solution 1 for OAI.QuadraticDivisorSplit.sum_divisors_coprime_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T01:21:52.683083+00:00
-- url     : https://prove2.me/submissions/8309102e-04cd-4c06-acb9-cdb6ca072e0e

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Theorems.Thm_OAI_QuadraticDivisorSplit_split_product_injective
import Theorems.Thm_OAI_QuadraticDivisorSplit_divisors_coprime_product

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
open scoped BigOperators Classical
open scoped BigOperators Classical
open OAI.QuadraticDivisorSplit
open IdealMobiusDivisorSum
namespace OAI.QuadraticDivisorSplit
theorem _root_.solution (B C : Ideal O) (hB : B ≠ 0) (hC : C ≠ 0)
    (hBC : IsCoprime B C) (f : Ideal O → ℂ) :
    (∑ D ∈ idealDivisors (B * C), f D) =
      ∑ D₁ ∈ idealDivisors B, ∑ D₂ ∈ idealDivisors C, f (D₁ * D₂) := by
  rw [divisors_coprime_product B C hB hC hBC, Finset.sum_image]
  · exact Finset.sum_product _ _ _
  · intro x hx y hy hxy
    have hx' : x.1 ∣ B ∧ x.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2⟩
    have hy' : y.1 ∣ B ∧ y.2 ∣ C :=
      ⟨(mem_idealDivisors hB).mp (Finset.mem_product.mp hy).1,
        (mem_idealDivisors hC).mp (Finset.mem_product.mp hy).2⟩
    have he : (⟨x, hx'⟩ : {z : Ideal O × Ideal O // z.1 ∣ B ∧ z.2 ∣ C}) = ⟨y, hy'⟩ :=
      split_product_injective B C hBC hxy
    exact congrArg Subtype.val he
end OAI.QuadraticDivisorSplit
