-- Prove2me | solution 1 for OAI.LocalLogFourier.coupled_positive_log_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:59:32.243104+00:00
-- url     : https://prove2.me/submissions/5d241a57-0da0-4be6-a349-b937a77210dd

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_LocalLogFourier_positive_log_separation
import Theorems.Thm_OAI_FourierBridge_logPhase_sum

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
    {ι : Type*} [Fintype ι]
    (W : ι → ℝ → ℂ) (F V : ℝ → ℂ) (R : ℝ)
    (a y : ι → ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R)
    (hactive : (∏ j : ι, W j (y j)) ≠ 0 →
      V (∑ j : ι, a j * y j) = 1) :
    (∏ j : ι, W j (y j)) *
      F (R * Real.exp (∑ j : ι, a j * y j)) =
      ∫ t : ℝ,
        (∏ j : ι, W j (y j) *
          FourierBridge.logPhase t (a j * y j)) *
          (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t := by
  classical
  let s : ℝ := ∑ j : ι, a j * y j
  let P : ℂ := ∏ j : ι, W j (y j)
  let b := 𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)
  have hsep : V s * F (R * Real.exp s) =
      ∫ t : ℝ, FourierBridge.logPhase t s * b t := by
    calc
      V s * F (R * Real.exp s) =
          ∫ t : ℝ, Complex.exp
            (↑(2 * Real.pi * inner ℝ t s) * Complex.I) * b t := by
        simpa [b] using
          (positive_log_separation V F R s hVc hVs hFpos hR)
      _ = ∫ t : ℝ, FourierBridge.logPhase t s * b t := by
        apply integral_congr_ae
        filter_upwards [] with t
        congr 1
        simp only [FourierBridge.logPhase, Real.inner_apply]
        congr 1
        push_cast
        ring
  have hcut : P * F (R * Real.exp s) =
      P * (V s * F (R * Real.exp s)) := by
    by_cases hP : P = 0
    · simp [hP]
    · rw [hactive (by simpa [P, s] using hP)]
      ring
  calc
    P * F (R * Real.exp s) = P * (V s * F (R * Real.exp s)) := hcut
    _ = P * (∫ t : ℝ, FourierBridge.logPhase t s * b t) := by rw [hsep]
    _ = ∫ t : ℝ, P * (FourierBridge.logPhase t s * b t) := by
      rw [integral_const_mul]
    _ = ∫ t : ℝ,
          (∏ j : ι, W j (y j) * FourierBridge.logPhase t (a j * y j)) * b t := by
      apply integral_congr_ae
      filter_upwards [] with t
      rw [show FourierBridge.logPhase t s =
          ∏ j : ι, FourierBridge.logPhase t (a j * y j) by
        simpa [s] using FourierBridge.logPhase_sum
          (Finset.univ : Finset ι) t (fun j => a j * y j)]
      rw [Finset.prod_mul_distrib]
      simp only [P]
      ring
end OAI.LocalLogFourier
