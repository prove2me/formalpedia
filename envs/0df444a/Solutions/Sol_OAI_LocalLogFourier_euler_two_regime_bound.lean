-- Prove2me | solution 1 for OAI.LocalLogFourier.euler_two_regime_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:57:44.469437+00:00
-- url     : https://prove2.me/submissions/63b42d50-abbb-4131-a0fd-f78f40400292

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles

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
open ActualEisensteinCubic
open ActualEisensteinCubic
open Filter
open scoped Topology
open ActualEisensteinCubic
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
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open OAI.LocalLogFourier
namespace OAI.LocalLogFourier
theorem _root_.solution
    (F : ℝ → ℂ) (A K : ℕ) (Csmall Clarge : ℝ)
    (hCs : 0 ≤ Csmall) (hCl : 0 ≤ Clarge)
    (hsmall : ∀ i ≤ K, ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖eulerDeriv F i x‖ ≤ Csmall)
    (hlarge : ∀ i ≤ K, ∀ x : ℝ, 1 ≤ x →
      x ^ A * ‖eulerDeriv F i x‖ ≤ Clarge)
    (i : ℕ) (hi : i ≤ K) (x : ℝ) (hx : 0 < x) :
    (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
      (2 : ℝ) ^ A * (Csmall + Clarge) := by
  by_cases hsmallx : x ≤ 1
  · have hpow : (1 + x) ^ A ≤ (2 : ℝ) ^ A := by gcongr; linarith
    calc
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
        (2 : ℝ) ^ A * ‖eulerDeriv F i x‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ (2 : ℝ) ^ A * Csmall :=
        mul_le_mul_of_nonneg_left (hsmall i hi x hx hsmallx) (by positivity)
      _ ≤ (2 : ℝ) ^ A * (Csmall + Clarge) := by gcongr; linarith
  · have hx1 : 1 ≤ x := le_of_lt (lt_of_not_ge hsmallx)
    have hpow : (1 + x) ^ A ≤ ((2 : ℝ) * x) ^ A := by
      gcongr
      linarith
    calc
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤
        ((2 : ℝ) * x) ^ A * ‖eulerDeriv F i x‖ :=
        mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = (2 : ℝ) ^ A * (x ^ A * ‖eulerDeriv F i x‖) := by rw [mul_pow]; ring
      _ ≤ (2 : ℝ) ^ A * Clarge :=
        mul_le_mul_of_nonneg_left (hlarge i hi x hx1) (by positivity)
      _ ≤ (2 : ℝ) ^ A * (Csmall + Clarge) := by gcongr; linarith
end OAI.LocalLogFourier
