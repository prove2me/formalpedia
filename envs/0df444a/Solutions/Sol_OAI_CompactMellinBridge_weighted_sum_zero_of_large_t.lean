-- Prove2me | solution 1 for OAI.CompactMellinBridge.weighted_sum_zero_of_large_t
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:18:39.451326+00:00
-- url     : https://prove2.me/submissions/3b3296d4-bdb2-4cad-9904-311d7178ccd7

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_PrimeExtraction
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_FiniteEulerRestoration
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
open OAI.CompactMellinBridge
namespace OAI.CompactMellinBridge
theorem _root_.solution
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W F : ℝ → ℂ)
    (hW : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (t : ℝ) (ht : 2 ≤ t) : F t = 0 := by
  have hterm (n : ℕ) : a n * W ((n : ℝ) * t) = 0 := by
    by_cases hn : n = 0
    · simp [hn, ha0]
    · have hn1 : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hnt : 2 ≤ (n : ℝ) * t := by
        calc
          2 ≤ t := ht
          _ = (1 : ℝ) * t := by ring
          _ ≤ (n : ℝ) * t :=
            mul_le_mul_of_nonneg_right hn1 (by linarith)
      simp [hW _ hnt]
  have hzero : HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) 0 := by
    simpa only [hterm] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  exact (hF t (lt_of_lt_of_le (by norm_num) ht)).unique hzero
end OAI.CompactMellinBridge
