-- Prove2me | solution 1 for OAI.FiniteSFactor.restore_two_primes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:35.208556+00:00
-- url     : https://prove2.me/submissions/5b04d56e-ea1d-45f2-b241-da5ede64fcf5

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_FiniteSFactor_restore_insert_prime
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open OAI.FiniteSFactor
namespace OAI.FiniteSFactor
theorem _root_.solution (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (hne : P ≠ Q) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (n : ℕ) :
    outsideCoeff ∅ w n =
      (outsideCoeff (insert Q {P}) w n +
        (if Ideal.absNorm Q ∣ n then
          w Q * outsideCoeff (insert Q {P}) w (n / Ideal.absNorm Q) else 0)) +
      (if Ideal.absNorm P ∣ n then
        w P *
          (outsideCoeff (insert Q {P}) w (n / Ideal.absNorm P) +
            (if Ideal.absNorm Q ∣ n / Ideal.absNorm P then
              w Q * outsideCoeff (insert Q {P}) w
                ((n / Ideal.absNorm P) / Ideal.absNorm Q) else 0))
        else 0) := by
  classical
  have hPnot : P ∉ (∅ : Finset (Ideal O)) := by simp
  have hSprime : ∀ R ∈ ({P} : Finset (Ideal O)), Prime R := by
    intro R hR
    have heq : R = P := Finset.mem_singleton.mp hR
    exact heq ▸ hP
  have hQnot : Q ∉ ({P} : Finset (Ideal O)) := by simpa using hne.symm
  have hfirst := restore_insert_prime ∅ (by simp) P hP hPnot w hzero hmul n
  have hsecond := restore_insert_prime {P} hSprime Q hQ hQnot w hzero hmul n
  have hthird := restore_insert_prime {P} hSprime Q hQ hQnot w hzero hmul
    (n / Ideal.absNorm P)
  simp only [Finset.insert_empty] at hfirst
  rw [hsecond, hthird] at hfirst
  exact hfirst
end OAI.FiniteSFactor
