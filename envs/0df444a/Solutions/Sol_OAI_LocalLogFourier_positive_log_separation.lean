-- Prove2me | solution 1 for OAI.LocalLogFourier.positive_log_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:58:33.566991+00:00
-- url     : https://prove2.me/submissions/8c98d800-730e-49d0-80a3-6ffbac17138a

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_positiveLogProfile_apply
import Theorems.Thm_OAI_FourierBridge_schwartz_log_inversion

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
    (V F : ℝ → ℂ) (R s : ℝ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V)
    (hFpos : ContDiffOn ℝ ∞ F (Set.Ioi 0))
    (hR : 0 < R) :
    V s * F (R * Real.exp s) =
      ∫ t : ℝ, Complex.exp (↑(2 * Real.pi * inner ℝ t s) * Complex.I) *
        (𝓕 (positiveLogProfile V F R hVc hVs hFpos hR)) t := by
  rw [← positiveLogProfile_apply V F R s hVc hVs hFpos hR]
  exact FourierBridge.schwartz_log_inversion _ _
end OAI.LocalLogFourier
