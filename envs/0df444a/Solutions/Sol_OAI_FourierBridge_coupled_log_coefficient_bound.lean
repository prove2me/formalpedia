-- Prove2me | solution 1 for OAI.FourierBridge.coupled_log_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:35:18.659226+00:00
-- url     : https://prove2.me/submissions/be1e87fa-eb53-461b-96c3-24b470a5302d

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_profileMomentConstant_nonneg
import Theorems.Thm_OAI_FourierBridge_profileMomentConstant_dominates
import Theorems.Thm_OAI_FourierBridge_uniform_logProfile_source_pair
import Theorems.Thm_OAI_FourierBridge_uniform_fourier_one_plus_moment

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
    (V F : ℝ → ℂ) (R m H L CW CF : ℝ) (A J : ℕ)
    (hVc : HasCompactSupport V)
    (hVs : ContDiff ℝ ∞ V) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (hL : 0 ≤ L)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hVderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i V y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i V y‖ ≠ 0) →
        m ≤ Real.exp y ∧ Real.exp y ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, (1 + ‖t‖) ^ J *
        ‖(𝓕 (logProfile V F R 1 hVc hVs hFs)) t‖) ≤
      (2 : ℝ) ^ J *
        (coefficientMomentBound 0
          (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF) +
        coefficientMomentBound J
          (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF)) := by
  apply uniform_fourier_one_plus_moment _ J _ _ (by positivity)
    (profileMomentConstant_nonneg _ L H CW CF hL hCW hCF)
  intro i hi
  exact uniform_logProfile_source_pair V F R 1 m H L CW CF
    (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
      L H CW CF) A
    (J + (volume : Measure ℝ).integrablePower) i
    hVc hVs hFs hR hm hm1 hH (by simpa using hH)
    hL hCW hCF hi hVderiv
    (by simpa only [one_mul] using hwindow)
    hFdecay
    (by intro j hj
        exact profileMomentConstant_dominates _ j L H CW CF
          hL hCW hCF hj)
end OAI.FourierBridge
