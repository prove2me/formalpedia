-- Prove2me | solution 1 for OAI.CompactMellinBridge.outsideCompactSum_hasSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:38.309202+00:00
-- url     : https://prove2.me/submissions/f5eb02a9-4c7c-4fd0-8ed5-59f6454178cb

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
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
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal FiniteSFactor.O)) (W : ℝ → ℂ)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (t : ℝ) (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
        W ((n : ℝ) * t)) (outsideCompactSum χ S W t) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / t)
  have htail (n : ℕ) (hn : n ∉ Finset.range N) :
      FiniteSFactor.outsideCoeff S (ShortDraftHeckeBridge.baseChangeWeight χ) n *
        W ((n : ℝ) * t) = 0 := by
    have hnNat : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hnNat
    have hNt : 2 ≤ (N : ℝ) * t := by
      have h := mul_lt_mul_of_pos_right hN ht
      have hcancel : (2 / t) * t = 2 := by
        field_simp
      rw [hcancel] at h
      exact h.le
    have hnt : 2 ≤ (n : ℝ) * t :=
      hNt.trans (mul_le_mul_of_nonneg_right hnReal ht.le)
    simp [hsupp _ hnt]
  exact (summable_of_ne_finset_zero htail).hasSum
end OAI.CompactMellinBridge
