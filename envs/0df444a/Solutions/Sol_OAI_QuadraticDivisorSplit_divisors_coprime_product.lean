-- Prove2me | solution 1 for OAI.QuadraticDivisorSplit.divisors_coprime_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T00:56:13.412196+00:00
-- url     : https://prove2.me/submissions/b8b0188b-f064-483c-af5f-299f7045c97e

import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_LocalBrackets
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_RayExpansion
import Theorems.Thm_OAI_QuadraticDivisorSplit_exists_unique_split

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
    (hBC : IsCoprime B C) :
    idealDivisors (B * C) =
      ((idealDivisors B) ×ˢ (idealDivisors C)).image (fun x => x.1 * x.2) := by
  ext D
  rw [mem_idealDivisors (mul_ne_zero hB hC), Finset.mem_image]
  constructor
  · intro hD
    obtain ⟨x, hx, _⟩ := exists_unique_split B C D hBC hD
    exact ⟨x, Finset.mem_product.mpr
      ⟨(mem_idealDivisors hB).mpr hx.1, (mem_idealDivisors hC).mpr hx.2.1⟩, hx.2.2⟩
  · rintro ⟨x, hx, rfl⟩
    exact mul_dvd_mul ((mem_idealDivisors hB).mp (Finset.mem_product.mp hx).1)
      ((mem_idealDivisors hC).mp (Finset.mem_product.mp hx).2)
end OAI.QuadraticDivisorSplit
