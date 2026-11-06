-- Prove2me | solution 1 for OAI.FourierBridge.logProfile_pointwise_decay
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:53.834938+00:00
-- url     : https://prove2.me/submissions/151012e3-cb63-4ac1-8e3a-814a3a5818ce

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles

set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open scoped ContDiff Manifold
open OAI.FourierBridge
namespace OAI.FourierBridge
theorem _root_.solution
    (W F : ℝ → ℂ) (R a m CW CF : ℝ) (A : ℕ)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWbound : ∀ y, ‖W y‖ ≤ CW)
    (hlower : ∀ y, W y ≠ 0 → m ≤ Real.exp (a * y))
    (hFdecay : ∀ u, 0 ≤ u → (1 + u) ^ A * ‖F u‖ ≤ CF)
    (y : ℝ) :
    m ^ A * (1 + R) ^ A * ‖W y * F (R * Real.exp (a * y))‖ ≤
      CW * CF := by
  by_cases hWy : W y = 0
  · simp [hWy, mul_nonneg hCW hCF]
  have hE : m ≤ Real.exp (a * y) := hlower y hWy
  have hu : 0 ≤ R * Real.exp (a * y) := by positivity
  have hscale : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hE)]
  have hpow : (m * (1 + R)) ^ A ≤
      (1 + R * Real.exp (a * y)) ^ A := by gcongr
  have hbase : (m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖ ≤ CF :=
    (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
      (hFdecay _ hu)
  rw [Complex.norm_mul]
  calc
    m ^ A * (1 + R) ^ A * (‖W y‖ * ‖F (R * Real.exp (a * y))‖) =
      ‖W y‖ * ((m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖) := by rw [mul_pow]; ring
    _ ≤ CW * ((m * (1 + R)) ^ A * ‖F (R * Real.exp (a * y))‖) :=
      mul_le_mul_of_nonneg_right (hWbound y) (by positivity)
    _ ≤ CW * CF := mul_le_mul_of_nonneg_left hbase hCW
end OAI.FourierBridge
