-- Prove2me | solution 1 for OAI.FourierBridge.uniform_logProfile_coefficient_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:16.80433+00:00
-- url     : https://prove2.me/submissions/f607263b-1c5b-4d9b-84c0-b93a36e0290a

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_uniform_fourier_coefficient_moment
import Theorems.Thm_OAI_FourierBridge_uniform_logProfile_source_pair

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
    (W F : ℝ → ℂ) (R a m H L CW CF C : ℝ) (A J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) (hC : 0 ≤ C)
    (hWderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF)
    (hCbound : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant j H CW CF ≤ C) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, ‖t‖ ^ J *
        ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) * C) := by
  apply uniform_fourier_coefficient_moment _ J _ C (by positivity) hC
  intro i hi
  exact uniform_logProfile_source_pair W F R a m H L CW CF C A
    (J + (volume : Measure ℝ).integrablePower) i
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF hi
    hWderiv hwindow hFdecay hCbound
end OAI.FourierBridge
