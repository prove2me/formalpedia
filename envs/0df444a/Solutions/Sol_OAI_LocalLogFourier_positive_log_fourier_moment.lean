-- Prove2me | solution 1 for OAI.LocalLogFourier.positive_log_fourier_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:02:25.166715+00:00
-- url     : https://prove2.me/submissions/1238a602-2be8-4784-b201-0a0c5e06057d

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_LocalLogFourier_momentConstant_nonneg
import Theorems.Thm_OAI_LocalLogFourier_momentConstant_dominates
import Theorems.Thm_OAI_LocalLogFourier_positive_log_source_pair
import Theorems.Thm_OAI_FourierBridge_uniform_fourier_one_plus_moment

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
    (V F : ℝ → ℂ) (R m Lwin CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hL : 0 ≤ Lwin) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ s,
      ‖iteratedFDeriv ℝ i V s‖ ≤ CW)
    (hwindow : ∀ s,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V s‖ ≠ 0) →
        m ≤ Real.exp s ∧ |s| ≤ Lwin)
    (hEuler : ∀ i ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ x : ℝ, 0 < x →
        (1 + x) ^ A * ‖eulerDeriv F i x‖ ≤ CF) :
    (m ^ A * (1 + R) ^ A) *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t‖) ≤
      (2 : ℝ) ^ J *
        (FourierBridge.coefficientMomentBound 0
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF) +
         FourierBridge.coefficientMomentBound J
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF)) := by
  let K := J + (volume : Measure ℝ).integrablePower
  let C := momentConstant K Lwin CW CF
  have hC : 0 ≤ C := momentConstant_nonneg K Lwin CW CF hL hCW hCF
  apply FourierBridge.uniform_fourier_one_plus_moment _ J _ C (by positivity) hC
  intro n hn
  exact positive_log_source_pair V F R m Lwin CW CF C A K n
    hVc hVs hFpos hR hm hm1 hL hCW hCF
    (by simpa [K] using hn)
    (by simpa [K] using hVderiv)
    (by simpa [K] using hwindow)
    (by simpa [K] using hEuler)
    (by
      intro j hj
      simpa [C] using momentConstant_dominates K j Lwin CW CF hL hCW hCF hj)
end OAI.LocalLogFourier
