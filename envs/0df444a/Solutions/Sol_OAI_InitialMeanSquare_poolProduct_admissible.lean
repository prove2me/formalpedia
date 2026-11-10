-- Prove2me | solution 1 for OAI.InitialMeanSquare.poolProduct_admissible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T11:56:08.784438+00:00
-- url     : https://prove2.me/submissions/f6cfd60e-9023-4566-8028-e53d90070f2b

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_DirichletForm
import Definitions.Def_OAI_NumberTheory_DirichletL_MeanSquare_InputEnergy
import Theorems.Thm_OAI_CanonicalQuadraticSieve_poolOdd


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
open scoped BigOperators Classical SchwartzMap ContDiff
open OAI.InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)
namespace OAI.InitialMeanSquare
theorem _root_.solution (F : Finset (Ideal O)) (hF : ∀ I ∈ F, Admissible I)
    (S : Finset (primePool F)) : Admissible (∏ i ∈ S,i.val) := by
  have hp (i : primePool F) : Prime i.val :=
    Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏ i ∈ S,i.val) ≠ (0 : Ideal O) :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)
  refine ⟨hn, ?_, ?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))).isRelPrime
    · intro i hi
      exact (hp i).squarefree
  · intro P hP
    obtain ⟨hprime, hdiv⟩ := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hP
    obtain ⟨i, hi, hPi⟩ := (hprime.dvd_finsetProd_iff (fun i : primePool F => i.val)).mp hdiv
    have he : P=i.val := (prime_dvd_prime_iff_eq hprime (hp i)).mp hPi
    rw [he]
    exact ⟨poolGood F hF i, poolOdd F hF i⟩
end OAI.InitialMeanSquare
