-- Prove2me | solution 1 for OAI.CompactMellinBridge.weighted_sum_continuousOn_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:23.664206+00:00
-- url     : https://prove2.me/submissions/a3a3ba32-3106-4ab8-b6d2-f4f88b37695d

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
theorem _root_.solution
    (a : ℕ → ℂ) (W F : ℝ → ℂ)
    (hW : ContDiff ℝ (↑(⊤ : ℕ∞)) W)
    (hsupp : ∀ y : ℝ, 2 ≤ y → W y = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t)) :
    ContinuousOn F (Set.Ioi (0 : ℝ)) := by
  intro t0 ht0
  have ht0pos : 0 < t0 := ht0
  obtain ⟨N, hN⟩ := exists_nat_gt (4 / t0)
  have hNmul := mul_lt_mul_of_pos_right hN (by positivity : 0 < t0 / 2)
  have hNtwo : 2 < (N : ℝ) * (t0 / 2) := by
    have hdiv : (4 / t0) * (t0 / 2) = 2 := by
      field_simp
      ring
    rw [hdiv] at hNmul
    exact hNmul
  have hsumEq (u : ℝ) (hu : t0 / 2 ≤ u) :
      F u = ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u) := by
    have hupos : 0 < u := lt_of_lt_of_le (by positivity : 0 < t0 / 2) hu
    have htail (n : ℕ) (hn : n ∉ Finset.range N) :
        a n * W ((n : ℝ) * u) = 0 := by
      have hnNat : N ≤ n := Nat.le_of_not_gt (by simpa using hn)
      have hnReal : (N : ℝ) ≤ n := by exact_mod_cast hnNat
      have hnu : 2 ≤ (n : ℝ) * u := by
        calc
          2 ≤ (N : ℝ) * (t0 / 2) := hNtwo.le
          _ ≤ (N : ℝ) * u :=
            mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg (α := ℝ) N)
          _ ≤ (n : ℝ) * u :=
            mul_le_mul_of_nonneg_right hnReal hupos.le
      simp [hsupp _ hnu]
    calc
      F u = ∑' n : ℕ, a n * W ((n : ℝ) * u) := (hF u hupos).tsum_eq.symm
      _ = ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u) :=
        tsum_eq_sum htail
  have hcontW : Continuous W := hW.continuous
  have hcontSum : Continuous
      (fun u : ℝ => ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u)) := by
    fun_prop
  have hevent : F =ᶠ[𝓝 t0]
      (fun u : ℝ => ∑ n ∈ Finset.range N, a n * W ((n : ℝ) * u)) := by
    filter_upwards [Ioi_mem_nhds (by linarith : t0 / 2 < t0)] with u hu
    exact hsumEq u hu.le
  exact (hcontSum.continuousAt.congr_of_eventuallyEq hevent).continuousWithinAt
end OAI.CompactMellinBridge
