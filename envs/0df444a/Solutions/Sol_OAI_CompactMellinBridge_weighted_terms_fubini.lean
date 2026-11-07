-- Prove2me | solution 1 for OAI.CompactMellinBridge.weighted_terms_fubini
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:45:35.491592+00:00
-- url     : https://prove2.me/submissions/5ac4b024-c082-4b6f-b43b-a1115658cb72

import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_FiniteEulerFactors
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_CompactScale
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
namespace CompactScaleBridge
open ConcretePrimeRowBridge ShortDraftHeckeBridge Filter Asymptotics
end CompactScaleBridge
open Filter Asymptotics MeasureTheory
open scoped Topology
namespace CompactMellinBridge
private theorem weighted_norm_scale
    (a : ℂ) (W : ℝ → ℂ) (s : ℂ)
    (N t : ℝ) (hN : 0 < N) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) * (a * W (N * t))‖ =
      (‖a‖ / N ^ (s.re - 1)) *
        ‖(N * t : ℂ) ^ (s - 1) * W (N * t)‖ := by
  have hNt : 0 < N * t := mul_pos hN ht
  have hNpow : 0 < N ^ (s.re - 1) := Real.rpow_pos_of_pos hN _
  rw [norm_mul, norm_mul, norm_mul]
  rw [← Complex.ofReal_mul]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.norm_cpow_eq_rpow_re_of_pos hNt]
  simp only [Complex.sub_re, Complex.one_re]
  rw [Real.mul_rpow hN.le ht.le]
  field_simp
private theorem weighted_norm_integral
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (n : ℕ) :
    (∫ t : ℝ in Set.Ioi 0,
      ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) =
    ‖LSeries.term a s n‖ *
      (∫ u : ℝ in Set.Ioi 0,
        ‖(u : ℂ) ^ (s - 1) * W u‖) := by
  by_cases hn : n = 0
  · subst n
    simp [ha0, LSeries.term_zero]
  · have hN : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    let G : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (s - 1) * W u‖
    have hscale :
        (∫ t : ℝ in Set.Ioi 0,
          ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) =
          (‖a n‖ / (n : ℝ) ^ (s.re - 1)) *
            (∫ t : ℝ in Set.Ioi 0, G ((n : ℝ) * t)) := by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simpa only [G, Complex.ofReal_mul] using
        weighted_norm_scale (a n) W s n t hN ht
    rw [hscale, integral_comp_mul_left_Ioi G 0 hN]
    simp only [mul_zero, smul_eq_mul]
    have hpow : (n : ℝ) ^ (s.re - 1) * (n : ℝ) =
        (n : ℝ) ^ s.re := by
      calc
        (n : ℝ) ^ (s.re - 1) * (n : ℝ) =
            (n : ℝ) ^ (s.re - 1) * (n : ℝ) ^ (1 : ℝ) := by
              rw [Real.rpow_one]
        _ = (n : ℝ) ^ ((s.re - 1) + 1) :=
          (Real.rpow_add hN (s.re - 1) 1).symm
        _ = (n : ℝ) ^ s.re := by congr 1; ring
    rw [LSeries.norm_term_eq]
    simp only [if_neg hn, G]
    have hinv : ((n : ℝ) ^ (s.re - 1))⁻¹ * (n : ℝ)⁻¹ =
        ((n : ℝ) ^ s.re)⁻¹ := by
      rw [← mul_inv_rev, mul_comm, hpow]
    simp only [div_eq_mul_inv]
    calc
      ‖a n‖ * ((n : ℝ) ^ (s.re - 1))⁻¹ *
          ((n : ℝ)⁻¹ *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖)) =
          (‖a n‖ * (((n : ℝ) ^ (s.re - 1))⁻¹ * (n : ℝ)⁻¹)) *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖) := by ring
      _ = (‖a n‖ * ((n : ℝ) ^ s.re)⁻¹) *
            (∫ u : ℝ in Set.Ioi 0, ‖(u : ℂ) ^ (s - 1) * W u‖) := by rw [hinv]
end CompactMellinBridge
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
    (a : ℕ → ℂ) (ha0 : a 0 = 0) (W : ℝ → ℂ)
    (s : ℂ) (hlsum : LSeriesSummable a s) :
    Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖) := by
  let C : ℝ := ∫ u : ℝ in Set.Ioi 0,
    ‖(u : ℂ) ^ (s - 1) * W u‖
  have hnorm : Summable (fun n : ℕ => ‖LSeries.term a s n‖) := hlsum.norm
  have hsum : Summable (fun n : ℕ => ‖LSeries.term a s n‖ * C) :=
    hnorm.mul_right C
  exact hsum.congr (fun n => (weighted_norm_integral a ha0 W s n).symm)
end OAI.CompactMellinBridge
