-- Prove2me | solution 1 for OAI.ShortDraftHeckeBridge.tsum_eq_one_sub_mul_tsum_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:13:27.17375+00:00
-- url     : https://prove2.me/submissions/b51e482d-1694-4bee-8643-91a403fa9f19

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_NormFiberCharacters
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_LocalEulerIdentities
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
open OAI.ShortDraftHeckeBridge
namespace OAI.ShortDraftHeckeBridge
theorem _root_.solution
    (a : ℕ → ℂ) (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hf : Summable (fun n : ℕ => a n * (r : ℂ) ^ n)) :
    (∑' n : ℕ, a n * (r : ℂ) ^ n) =
      (1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n) := by
  have hrC : ‖(r : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have hg : Summable (fun n : ℕ => (r : ℂ) ^ n) :=
    summable_geometric_of_norm_lt_one hrC
  have hconv := hasSum_sum_range_mul_of_summable_norm hf.norm hg.norm
  have hcoeff (n : ℕ) :
      (∑ k ∈ Finset.range (n + 1),
        (a k * (r : ℂ) ^ k) * (r : ℂ) ^ (n - k)) =
      prefixCoeff a n * (r : ℂ) ^ n := by
    calc
      (∑ k ∈ Finset.range (n + 1),
        (a k * (r : ℂ) ^ k) * (r : ℂ) ^ (n - k)) =
          ∑ k ∈ Finset.range (n + 1), a k * (r : ℂ) ^ n := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hkn]
      _ = prefixCoeff a n * (r : ℂ) ^ n := by
        rw [prefixCoeff, Finset.sum_mul]
  have hconvEq := hconv.tsum_eq
  simp_rw [hcoeff] at hconvEq
  rw [tsum_geometric_of_norm_lt_one hrC] at hconvEq
  have hne : (1 - (r : ℂ)) ≠ 0 := by
    exact sub_ne_zero.mpr (by norm_cast; exact (ne_of_lt hr1).symm)
  calc
    (∑' n : ℕ, a n * (r : ℂ) ^ n) =
      (1 - (r : ℂ)) *
        ((∑' n : ℕ, a n * (r : ℂ) ^ n) * (1 - (r : ℂ))⁻¹) := by
          field_simp
    _ = (1 - (r : ℂ)) * (∑' n : ℕ, prefixCoeff a n * (r : ℂ) ^ n) := by
      rw [hconvEq]
end OAI.ShortDraftHeckeBridge
