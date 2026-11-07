-- Prove2me | solution 1 for OAI.CompactMellinBridge.mellin_weighted_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T07:17:54.909548+00:00
-- url     : https://prove2.me/submissions/aee57720-6140-4cea-87ac-537db0fab3c6

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
    (a : ℕ → ℂ) (W F : ℝ → ℂ) (s : ℂ)
    (ha0 : a 0 = 0)
    (hF : ∀ t : ℝ, 0 < t →
      HasSum (fun n : ℕ => a n * W ((n : ℝ) * t)) (F t))
    (hint : ∀ n : ℕ,
      IntegrableOn
        (fun t : ℝ => (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)))
        (Set.Ioi 0))
    (hsumint : Summable (fun n : ℕ =>
      ∫ t : ℝ in Set.Ioi 0,
        ‖(t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))‖))
    (hlsum : LSeriesSummable a s) :
    mellin (fun D : ℝ => F D⁻¹) (-s) =
      mellin W s * LSeries a s := by
  have hterm (n : ℕ) :
      (∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        mellin W s * LSeries.term a s n := by
    by_cases hn : n = 0
    · subst n
      simp [ha0, LSeries.term_zero]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hscale := mellin_comp_mul_left W s hnpos
      have hmul : mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s =
          a n * mellin (fun t : ℝ => W ((n : ℝ) * t)) s := by
        simpa only [smul_eq_mul] using
          (mellin_const_smul (fun t : ℝ => W ((n : ℝ) * t)) s (a n))
      change mellin (fun t : ℝ => a n * W ((n : ℝ) * t)) s = _
      rw [hmul, hscale, LSeries.term_of_ne_zero hn]
      simp only [smul_eq_mul, Complex.ofReal_natCast, Complex.cpow_neg]
      ring
  have hsum :
      (∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))) =
        ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) :=
    integral_tsum_of_summable_integral_norm hint hsumint
  have hseries :
      (∑' n : ℕ, mellin W s * LSeries.term a s n) =
        mellin W s * LSeries a s := by
    simpa only [LSeries] using hlsum.hasSum.mul_left (mellin W s) |>.tsum_eq
  calc
    mellin (fun D : ℝ => F D⁻¹) (-s) = mellin F s := by
      simpa using mellin_comp_inv F (-s)
    _ = ∫ t : ℝ in Set.Ioi 0,
          ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := by
      unfold mellin
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      change (t : ℂ) ^ (s - 1) * F t =
        ∑' n : ℕ, (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t))
      rw [← (hF t ht).tsum_eq]
      rw [← tsum_mul_left]
    _ = ∑' n : ℕ, ∫ t : ℝ in Set.Ioi 0,
          (t : ℂ) ^ (s - 1) * (a n * W ((n : ℝ) * t)) := hsum.symm
    _ = ∑' n : ℕ, mellin W s * LSeries.term a s n := by simp_rw [hterm]
    _ = mellin W s * LSeries a s := hseries
end OAI.CompactMellinBridge
