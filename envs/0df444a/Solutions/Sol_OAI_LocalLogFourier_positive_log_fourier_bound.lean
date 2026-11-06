-- Prove2me | solution 1 for OAI.LocalLogFourier.positive_log_fourier_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:03:22.328706+00:00
-- url     : https://prove2.me/submissions/7cbd91ad-62f9-4399-8137-e464a6b0e8cf

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_LocalLogFourier_positive_log_fourier_moment
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
    (1 + R) ^ A *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t‖) ≤
      ((2 : ℝ) ^ J *
        (FourierBridge.coefficientMomentBound 0
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF) +
         FourierBridge.coefficientMomentBound J
          (momentConstant (J + (volume : Measure ℝ).integrablePower)
            Lwin CW CF))) / m ^ A := by
  have hpow : 0 < m ^ A := pow_pos hm _
  apply (le_div_iff₀ hpow).mpr
  have hbase := positive_log_fourier_moment V F R m Lwin CW CF A J
    hVc hVs hFpos hR hm hm1 hL hCW hCF hVderiv hwindow hEuler
  simpa [mul_assoc, mul_left_comm, mul_comm] using hbase
end OAI.LocalLogFourier
