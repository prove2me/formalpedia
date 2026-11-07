-- Prove2me | solution 1 for OAI.FiniteSFactor.restore_one_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:26.091261+00:00
-- url     : https://prove2.me/submissions/7087e7f9-50a9-41cb-98e4-0054d5caa877

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_FiniteSFactor_mem_goodFiber
import Theorems.Thm_OAI_FiniteSFactor_squarefree_prime_fiber_sum
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
private theorem sum_filter_squarefree (pred : Ideal O → Prop) (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0) (n : ℕ) :
    (∑ I ∈ fiber n, if pred I then w I else 0) =
      ∑ I ∈ (fiber n).filter (fun I => Squarefree I ∧ pred I), w I := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hsq : Squarefree I
  · simp [hsq]
  · simp [hsq, hzero I hsq]
open scoped Classical
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
namespace OAI.FiniteSFactor
theorem _root_.solution (P : Ideal O) (hP : Prime P)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ J, ¬P ∣ J → w (P * J) = w P * w J)
    (m : ℕ) :
    (∑ I ∈ fiber (Ideal.absNorm P * m), w I) =
      exceptPrimeCoeff P w (Ideal.absNorm P * m) +
        w P * exceptPrimeCoeff P w m := by
  classical
  let n := Ideal.absNorm P * m
  have hsplit : (∑ I ∈ fiber n, w I) =
      (∑ I ∈ fiber n, if ¬P ∣ I then w I else 0) +
      (∑ I ∈ fiber n, if P ∣ I then w I else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro I hI
    by_cases h : P ∣ I <;> simp [h]
  have hbad : (∑ I ∈ fiber n, if P ∣ I then w I else 0) =
      ∑ I ∈ badFiber P m, w I := by
    rw [badFiber]
    exact sum_filter_squarefree (fun I => P ∣ I) w hzero n
  have hgood : (∑ J ∈ goodFiber P m, w J) = exceptPrimeCoeff P w m := by
    rw [goodFiber, exceptPrimeCoeff, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro J hJ
    by_cases hsq : Squarefree J
    · simp [hsq]
    · simp [hsq, hzero J hsq]
  calc
    (∑ I ∈ fiber n, w I) =
        (∑ I ∈ fiber n, if ¬P ∣ I then w I else 0) +
          (∑ I ∈ fiber n, if P ∣ I then w I else 0) := hsplit
    _ = exceptPrimeCoeff P w n + ∑ I ∈ badFiber P m, w I := by
      rw [hbad]
      rfl
    _ = exceptPrimeCoeff P w n + ∑ J ∈ goodFiber P m, w (P * J) := by
      rw [squarefree_prime_fiber_sum P hP m w]
    _ = exceptPrimeCoeff P w n + w P * ∑ J ∈ goodFiber P m, w J := by
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro J hJ
      exact hmul J (mem_goodFiber.mp hJ).2.2
    _ = exceptPrimeCoeff P w n + w P * exceptPrimeCoeff P w m := by rw [hgood]
end OAI.FiniteSFactor
