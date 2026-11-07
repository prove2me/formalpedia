-- Prove2me | solution 1 for OAI.FiniteSFactor.outsideExpSum_restore_insert_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:22:45.146007+00:00
-- url     : https://prove2.me/submissions/c699124d-c8e2-48c7-8558-cce485662f4b

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Theorems.Thm_OAI_FiniteEulerRestoration_tsum_restore_one_prime_exp
import Theorems.Thm_OAI_FiniteSFactor_restore_insert_prime


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
open OAI.FiniteSFactor
namespace OAI.FiniteSFactor
theorem _root_.solution
    (S : Finset (Ideal O)) (hprime : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPnot : P ∉ S)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ I J, IsRelPrime I J → w (I * J) = w I * w J)
    (t : ℝ)
    (hbase : Summable (fun n : ℕ =>
      outsideCoeff (insert P S) w n * Real.exp (-(n : ℝ) * t)))
    (hscaled : Summable (fun n : ℕ =>
      outsideCoeff (insert P S) w n *
        Real.exp (-(n : ℝ) * ((Ideal.absNorm P : ℝ) * t)))) :
    outsideExpSum S w t = outsideExpSum (insert P S) w t +
      w P * outsideExpSum (insert P S) w ((Ideal.absNorm P : ℝ) * t) := by
  let N : ℕ := Ideal.absNorm P
  have hN : 0 < N :=
    Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have hcoeff (n : ℕ) :
      outsideCoeff S w n = outsideCoeff (insert P S) w n +
        (if N ∣ n then w P * outsideCoeff (insert P S) w (n / N) else 0) :=
    restore_insert_prime S hprime P hP hPnot w hzero hmul n
  unfold outsideExpSum
  exact FiniteEulerRestoration.tsum_restore_one_prime_exp hN
    (w P) (outsideCoeff S w) (outsideCoeff (insert P S) w)
    t hcoeff hbase hscaled
end OAI.FiniteSFactor
