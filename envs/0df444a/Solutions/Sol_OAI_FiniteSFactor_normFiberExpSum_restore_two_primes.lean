-- Prove2me | solution 1 for OAI.FiniteSFactor.normFiberExpSum_restore_two_primes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:46:08.352393+00:00
-- url     : https://prove2.me/submissions/a59dce0e-b9e8-422a-8ea4-73b015a59a60

import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_NormFiberExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Theorems.Thm_OAI_FiniteSFactor_outsideExpSum_restore_baseChange
import Theorems.Thm_OAI_FiniteSFactor_outsideExpSum_empty_eq_normFiberExpSum
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
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open OAI.FiniteSFactor
namespace OAI.FiniteSFactor
theorem _root_.solution {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q)
    (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q) (hPQ : P ≠ Q)
    (t : ℝ) (ht : 0 < t) :
    ShortDraftHeckeBridge.normFiberExpSum
      (ShortDraftHeckeBridge.baseChangeWeight χ) t =
        outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
        ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm P : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ P *
          ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * ((Ideal.absNorm P : ℝ) * t)) := by
  have hPnot : P ∉ (∅ : Finset (Ideal O)) := by simp
  have hQnot : Q ∉ ({P} : Finset (Ideal O)) := by simpa using hPQ.symm
  have hSP : ∀ R ∈ ({P} : Finset (Ideal O)), Prime R := by
    intro R hR
    simp only [Finset.mem_singleton] at hR
    subst R
    exact hP
  have hNP : (0 : ℝ) < (Ideal.absNorm P : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.1)
  have h0 := outsideExpSum_restore_baseChange χ ∅ (by simp) P hP hPnot t ht
  have h1 := outsideExpSum_restore_baseChange χ {P} hSP Q hQ hQnot t ht
  have h2 := outsideExpSum_restore_baseChange χ {P} hSP Q hQ hQnot
    ((Ideal.absNorm P : ℝ) * t) (mul_pos hNP ht)
  rw [outsideExpSum_empty_eq_normFiberExpSum] at h0
  simp only [Finset.insert_empty] at h0
  rw [h1, h2] at h0
  calc
    ShortDraftHeckeBridge.normFiberExpSum
        (ShortDraftHeckeBridge.baseChangeWeight χ) t =
      outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ) t +
      ShortDraftHeckeBridge.baseChangeWeight χ Q *
        outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
          ((Ideal.absNorm Q : ℝ) * t) +
      ShortDraftHeckeBridge.baseChangeWeight χ P *
        (outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
          ((Ideal.absNorm P : ℝ) * t) +
        ShortDraftHeckeBridge.baseChangeWeight χ Q *
          outsideExpSum (insert Q {P}) (ShortDraftHeckeBridge.baseChangeWeight χ)
            ((Ideal.absNorm Q : ℝ) * ((Ideal.absNorm P : ℝ) * t))) := h0
    _ = _ := by ring
end OAI.FiniteSFactor
