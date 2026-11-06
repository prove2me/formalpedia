-- Prove2me | solution 1 for OAI.LocalLogFourier.euler_derivative_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T04:58:34.116202+00:00
-- url     : https://prove2.me/submissions/7824a223-0833-444d-bd6a-a384d330b249

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Definitions.Def_OAI_NumberTheory_DirichletL_Fourier_PositiveLogProfiles
import Theorems.Thm_OAI_LocalLogFourier_iteratedDeriv_log_eq_euler

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
    (F : ℝ → ℂ) (R s m CF : ℝ) (A i : ℕ)
    (hR : 0 < R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hms : m ≤ Real.exp s)
    (hF : (1 + R * Real.exp s) ^ A *
      ‖eulerDeriv F i (R * Real.exp s)‖ ≤ CF) :
    m ^ A * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ i (fun z : ℝ => F (R * Real.exp z)) s‖ ≤ CF := by
  have hscale : m * (1 + R) ≤ 1 + R * Real.exp s := by
    nlinarith [mul_nonneg hR.le (sub_nonneg.mpr hms)]
  have hpow : (m * (1 + R)) ^ A ≤
      (1 + R * Real.exp s) ^ A := by gcongr
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    iteratedDeriv_log_eq_euler]
  calc
    m ^ A * (1 + R) ^ A * ‖eulerDeriv F i (R * Real.exp s)‖ =
      (m * (1 + R)) ^ A * ‖eulerDeriv F i (R * Real.exp s)‖ := by rw [mul_pow]
    _ ≤ (1 + R * Real.exp s) ^ A *
      ‖eulerDeriv F i (R * Real.exp s)‖ :=
      mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
    _ ≤ CF := hF
end OAI.LocalLogFourier
