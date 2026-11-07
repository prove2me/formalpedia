-- Prove2me | solution 1 for OAI.FiniteSFactor.restore_insert_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:21:23.032185+00:00
-- url     : https://prove2.me/submissions/65947a15-76bb-4c0a-8e2b-87b8824ddad3

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_FiniteSFactor_outsideWeight_mul
import Theorems.Thm_OAI_FiniteSFactor_restore_one_prime_all
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
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
namespace FiniteSFactor
open scoped Classical
open scoped Classical
private theorem outsideWeight_zero_of_not_squarefree (S : Finset (Ideal O))
    (w : Ideal O → ℂ) (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (I : Ideal O) (hsq : ¬Squarefree I) : outsideWeight S w I = 0 := by
  by_cases hg : ∀ P ∈ S, ¬P ∣ I
  · simp [outsideWeight,  hzero I hsq]
  · simp [outsideWeight, hg]
private theorem outsideWeight_prime_of_not_mem (S : Finset (Ideal O))
    (hprime : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P)
    (hPnot : P ∉ S) (w : Ideal O → ℂ) :
    outsideWeight S w P = w P := by
  have hgood : ∀ Q ∈ S, ¬Q ∣ P := by
    intro Q hQ hd
    have heq : Q = P :=
      associated_iff_eq.mp ((hprime Q hQ).associated_of_dvd hP hd)
    exact hPnot (heq ▸ hQ)
  change (if ∀ Q ∈ S, ¬Q ∣ P then w P else 0) = w P
  exact if_pos hgood
private theorem exceptPrimeCoeff_outsideWeight (S : Finset (Ideal O))
    (P : Ideal O) (w : Ideal O → ℂ) (n : ℕ) :
    exceptPrimeCoeff P (outsideWeight S w) n =
      outsideCoeff (insert P S) w n := by
  classical
  unfold exceptPrimeCoeff outsideCoeff
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hd : P ∣ I
  · simp [outsideWeight, hd]
  · by_cases hs : ∀ Q ∈ S, ¬Q ∣ I
    · simp [outsideWeight, hd]
    · simp [outsideWeight, hd, hs]
end FiniteSFactor
namespace ShortDraftHeckeBridge
end ShortDraftHeckeBridge
namespace DyadicTransfer
end DyadicTransfer
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
namespace FiniteSFactor
end FiniteSFactor
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
open OAI.FiniteSFactor
open scoped Classical
open scoped Classical
namespace OAI.FiniteSFactor
theorem _root_.solution (S : Finset (Ideal O))
    (hprime : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P)
    (hPnot : P ∉ S) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (n : ℕ) :
    outsideCoeff S w n = outsideCoeff (insert P S) w n +
      (if Ideal.absNorm P ∣ n then
        w P * outsideCoeff (insert P S) w (n / Ideal.absNorm P) else 0) := by
  have hzeroS : ∀ I, ¬Squarefree I → outsideWeight S w I = 0 :=
    outsideWeight_zero_of_not_squarefree S w hzero
  have hmulS : ∀ J, ¬P ∣ J →
      outsideWeight S w (P * J) = outsideWeight S w P * outsideWeight S w J := by
    intro J hnot
    apply outsideWeight_mul S hprime w P J
    exact hmul P J (hP.irreducible.isRelPrime_iff_not_dvd.mpr hnot)
  have hrest := restore_one_prime_all P hP (outsideWeight S w) hzeroS hmulS n
  unfold outsideCoeff at hrest ⊢
  rw [exceptPrimeCoeff_outsideWeight S P w n,
    exceptPrimeCoeff_outsideWeight S P w (n / Ideal.absNorm P),
    outsideWeight_prime_of_not_mem S hprime P hP hPnot w] at hrest
  exact hrest
end OAI.FiniteSFactor
