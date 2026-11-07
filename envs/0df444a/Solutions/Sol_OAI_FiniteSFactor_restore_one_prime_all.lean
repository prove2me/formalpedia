-- Prove2me | solution 1 for OAI.FiniteSFactor.restore_one_prime_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:20:00.487677+00:00
-- url     : https://prove2.me/submissions/e2036a51-c521-420f-91d8-abafe12e70f5

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Theorems.Thm_OAI_FiniteSFactor_restore_one_prime
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
open OAI.FiniteSFactor
open scoped Classical
namespace OAI.FiniteSFactor
theorem _root_.solution (P : Ideal O) (hP : Prime P)
    (w : Ideal O → ℂ)
    (hzero : ∀ I, ¬Squarefree I → w I = 0)
    (hmul : ∀ J, ¬P ∣ J → w (P * J) = w P * w J)
    (n : ℕ) :
    (∑ I ∈ fiber n, w I) = exceptPrimeCoeff P w n +
      (if Ideal.absNorm P ∣ n then
        w P * exceptPrimeCoeff P w (n / Ideal.absNorm P) else 0) := by
  classical
  by_cases hdiv : Ideal.absNorm P ∣ n
  · have hn : Ideal.absNorm P * (n / Ideal.absNorm P) = n :=
      Nat.mul_div_cancel' hdiv
    rw [← hn]
    have hPnorm : Ideal.absNorm P ≠ 0 :=
      (Ideal.absNorm_eq_zero_iff).not.mpr hP.ne_zero
    simpa [Nat.mul_div_cancel_left, hPnorm] using
      restore_one_prime P hP w hzero hmul (n / Ideal.absNorm P)
  · have hnone : ∀ I ∈ fiber n, ¬P ∣ I := by
      intro I hI hd
      apply hdiv
      have hnorm : Ideal.absNorm I = n := mem_fiber.mp hI
      rw [← hnorm]
      exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd)
    simp only [if_neg hdiv, add_zero]
    rw [exceptPrimeCoeff]
    apply Finset.sum_congr rfl
    intro I hI
    simp [hnone I hI]
end OAI.FiniteSFactor
