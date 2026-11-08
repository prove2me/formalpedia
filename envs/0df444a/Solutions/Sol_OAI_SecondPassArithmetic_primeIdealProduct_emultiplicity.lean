-- Prove2me | solution 1 for OAI.SecondPassArithmetic.primeIdealProduct_emultiplicity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T16:12:09.521558+00:00
-- url     : https://prove2.me/submissions/a0c8df7a-7910-40c2-b9f2-bd802c1dc8be

import Definitions.Def_OAI_NumberTheory_DirichletL_Eisenstein_SeedDefects
import Definitions.Def_OAI_NumberTheory_DirichletL_CubicSieve_GlobalEncoding

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
open OAI.SecondPassArithmetic
open ActualEisensteinCubic
variable {ι : Type*} [DecidableEq ι] (P : ι → Ideal OAI.SecondPassArithmetic.O)
  [∀ i, (P i).IsMaximal] (hinj : Function.Injective P)
include hinj
namespace OAI.SecondPassArithmetic
theorem _root_.solution (S : Finset ι) (v : ι → ℕ) (i : ι) :
    emultiplicity (P i) (∏ j ∈ S, P j ^ v j) = if i ∈ S then (v i : ℕ∞) else 0 := by
  have hp (j : ι) : Prime (P j) := Ideal.prime_of_isPrime (NeZero.ne (P j)) inferInstance
  rw [Finset.emultiplicity_prod (hp i)]
  have hz (j : ι) (hji : j ≠ i) : emultiplicity (P i) (P j ^ v j) = 0 := by
    rw [emultiplicity_pow (hp i), emultiplicity_eq_zero_of_irreducible_ne
      (hp i).irreducible (hp j).irreducible (fun he => hji (hinj he).symm), mul_zero]
  by_cases hi : i ∈ S
  · rw [if_pos hi,Finset.sum_eq_single i]
    · exact emultiplicity_pow_self_of_prime (hp i) (v i)
    · intro j hj hji
      exact hz j hji
    · exact fun hn => (hn hi).elim
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j hj
    exact hz j (fun he => hi (he ▸ hj))
end OAI.SecondPassArithmetic
