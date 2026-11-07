-- Prove2me | solution 1 for OAI.IdealDivisorBound.divisor_card_le_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:16:46.446534+00:00
-- url     : https://prove2.me/submissions/14af5e63-c8b2-4904-9d52-42d23ab287f1

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_SquarefreeDivisors
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_FiniteOperator
import Theorems.Thm_OAI_IdealDivisorBound_divisor_ne_zero

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
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open Filter IdealMobiusDivisorSum UniqueFactorizationMonoid
open OAI.IdealDivisorBound
namespace OAI.IdealDivisorBound
theorem _root_.solution (I : Ideal O) (hI : I ≠ ⊥) :
    (idealDivisors I).card ≤
      ∏ P ∈ primeSupport I, ((normalizedFactors I).count P + 1) := by
  change (idealDivisors I).card ≤
    ∏ P ∈ (normalizedFactors I).toFinset, ((normalizedFactors I).count P + 1)
  rw [← Multiset.card_Iic]
  apply Finset.card_le_card_of_injOn normalizedFactors
  · intro J hJ
    change normalizedFactors J ∈ Finset.Iic (normalizedFactors I)
    rw [Finset.mem_Iic]
    exact (dvd_iff_normalizedFactors_le_normalizedFactors
      (divisor_ne_zero hI hJ) hI).mp ((mem_idealDivisors hI).mp hJ)
  · intro J hJ K hK he
    calc
      J = (normalizedFactors J).prod := (Ideal.prod_normalizedFactors_eq_self (divisor_ne_zero hI hJ)).symm
      _ = (normalizedFactors K).prod := congrArg Multiset.prod he
      _ = K := Ideal.prod_normalizedFactors_eq_self (divisor_ne_zero hI hK)
end OAI.IdealDivisorBound
