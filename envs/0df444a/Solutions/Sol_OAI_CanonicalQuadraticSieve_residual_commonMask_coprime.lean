-- Prove2me | solution 1 for OAI.CanonicalQuadraticSieve.residual_commonMask_coprime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-08T19:48:30.701771+00:00
-- url     : https://prove2.me/submissions/4b5657db-6539-44b3-b248-96b000499302

import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CuspCoercivity
import Definitions.Def_OAI_NumberTheory_DirichletL_QuadraticSieve_CommonMasks
import Theorems.Thm_OAI_CanonicalQuadraticSieve_normalizedFactors_commonMaskIdeal
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_idealQuotient
import Theorems.Thm_OAI_CanonicalQuadraticSieve_admissible_of_dvd
import Theorems.Thm_OAI_CanonicalQuadraticSieve_commonMaskIdeal_squarefree
import Theorems.Thm_OAI_CanonicalQuadraticSieve_idealQuotient_mul
import Theorems.Thm_OAI_CanonicalQuadraticSieve_prime_good_iff_not_bad


set_option autoImplicit false
open OAI
noncomputable section
open OAI.CanonicalQuadraticSieve
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
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
namespace OAI.CanonicalQuadraticSieve
theorem _root_.solution (D I : Ideal O) (hI : Admissible I) (hDI : D∣I) :
    IsCoprime (commonMaskIdeal D) (idealQuotient D I) := by
  have hD := admissible_of_dvd hI hDI
  have hQ := admissible_idealQuotient hI hDI
  have hs : Squarefree (D*idealQuotient D I) := by rw [idealQuotient_mul hDI]; exact hI.2.1
  have hrel := (squarefree_mul_iff.mp hs).1
  have hG := (commonMaskIdeal_squarefree D).ne_zero
  apply ideals_coprime_of_relprime
  apply (UniqueFactorizationMonoid.isRelPrime_iff_no_prime_factors hG).mpr
  intro P hPG hPQ hp
  have hf : P∈UniqueFactorizationMonoid.normalizedFactors (commonMaskIdeal D) :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff hG).mpr ⟨hp,hPG⟩
  rw [normalizedFactors_commonMaskIdeal] at hf
  have hmem : P∈fixedBadPrimes ∨ P∈primeSupport D := Finset.mem_union.mp hf
  rcases hmem with hbad | hPD
  · let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
    have hfac : P∈UniqueFactorizationMonoid.normalizedFactors (idealQuotient D I) :=
      (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.1).mpr ⟨hp,hPQ⟩
    exact (prime_good_iff_not_bad P).mp (hQ.2.2 P hfac) hbad
  · have hd : P∣D := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hPD)
    exact hp.not_isUnit (hrel hd hPQ)
end OAI.CanonicalQuadraticSieve
