-- Prove2me | solution 1 for OAI.LocalLogFourier.positive_log_source_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:01:39.45202+00:00
-- url     : https://prove2.me/submissions/2c56e21d-a9bd-40c8-905b-004ac7693a53

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_LocalLogFourier_positive_log_uniform_seminorm
attribute [local simp] OAI.LocalLogFourier.positiveLogProfile_apply

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
    (V F : ℝ → ℂ) (R m Lwin CW CF C : ℝ) (A K n : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hn : n ≤ K)
    (hVderiv : ∀ i ≤ K, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ K, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ K, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF)
    (hCbound : ∀ j ≤ K,
      (1 + Lwin ^ (volume : Measure ℝ).integrablePower) *
        derivativeConstant j CW CF ≤ C) :
    (m ^ A * (1 + R) ^ A) *
      ((SchwartzMap.seminorm ℝ 0 n)
          (positiveLogProfile V F R hVc hVs hFpos hR) +
        (SchwartzMap.seminorm ℝ (volume : Measure ℝ).integrablePower n)
          (positiveLogProfile V F R hVc hVs hFpos hR)) ≤ C := by
  let p := (volume : Measure ℝ).integrablePower
  let D : ℝ := derivativeConstant n CW CF
  let g := positiveLogProfile V F R hVc hVs hFpos hR
  have hVderiv_n : ∀ i ≤ n, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW := by
    intro i hi s
    exact hVderiv i (hi.trans hn) s
  have hwindow_n : ∀ s,
      (∃ i ≤ n, ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin := by
    intro s hs
    obtain ⟨i, hi, hnonzero⟩ := hs
    exact hwindow s ⟨i, hi.trans hn, hnonzero⟩
  have hEuler_n : ∀ i ≤ n, ∀ x : ℝ, 0 < x →
      (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF := by
    intro i hi x hx
    exact hEuler i (hi.trans hn) x hx
  have hzero := positive_log_uniform_seminorm
    V F R m Lwin CW CF A n 0 hVc hVs hFpos hR hm hm1
    hL hCW hCF hVderiv_n hwindow_n hEuler_n
  have hp := positive_log_uniform_seminorm
    V F R m Lwin CW CF A n p hVc hVs hFpos hR hm hm1
    hL hCW hCF hVderiv_n hwindow_n hEuler_n
  calc
    (m ^ A * (1 + R) ^ A) *
        ((SchwartzMap.seminorm ℝ 0 n) g +
          (SchwartzMap.seminorm ℝ p n) g) =
        (m ^ A * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ 0 n) g +
        (m ^ A * (1 + R) ^ A) *
          (SchwartzMap.seminorm ℝ p n) g := by ring
    _ ≤ D + Lwin ^ p * D := by
      apply add_le_add
      · simpa [D, derivativeConstant, g] using hzero
      · simpa [D, derivativeConstant, g, p] using hp
    _ = (1 + Lwin ^ p) * D := by ring
    _ ≤ C := by simpa [D, p] using hCbound n hn
end OAI.LocalLogFourier
