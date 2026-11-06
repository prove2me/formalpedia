-- Prove2me | solution 1 for OAI.FourierBridge.uniform_logProfile_coefficient_moment_explicit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:29.095304+00:00
-- url     : https://prove2.me/submissions/2713d54c-188a-46e0-91f7-7f508b528d84

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_profileMomentConstant_nonneg
import Theorems.Thm_OAI_FourierBridge_profileMomentConstant_dominates
import Theorems.Thm_OAI_FourierBridge_uniform_logProfile_coefficient_moment

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
    (W F : ℝ → ℂ) (R a m H L CW CF : ℝ) (A J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W) (hFs : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF)
    (hWderiv : ∀ i ≤ J + (volume : Measure ℝ).integrablePower, ∀ y,
      ‖iteratedFDeriv ℝ i W y‖ ≤ CW)
    (hwindow : ∀ y,
      (∃ i ≤ J + (volume : Measure ℝ).integrablePower,
        ‖iteratedFDeriv ℝ i W y‖ ≠ 0) →
        m ≤ Real.exp (a * y) ∧
        Real.exp (a * y) ≤ H ∧ |y| ≤ L)
    (hFdecay : ∀ j ≤ J + (volume : Measure ℝ).integrablePower,
      ∀ i ≤ j, ∀ u, 0 ≤ u →
        (1 + u) ^ (A + j) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    (m ^ (A + (J + (volume : Measure ℝ).integrablePower)) *
      (1 + R) ^ A) *
      (∫ t : ℝ, ‖t‖ ^ J *
        ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((2 : ℝ) ^ 0 * (0 + 1) *
        (2 ^ (volume : Measure ℝ).integrablePower *
          ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
          profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF +
        (2 : ℝ) ^ (J + (volume : Measure ℝ).integrablePower) *
          (J + (volume : Measure ℝ).integrablePower + 1) *
          (2 ^ (volume : Measure ℝ).integrablePower *
            ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
          profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
            L H CW CF) := by
  apply uniform_logProfile_coefficient_moment W F R a m H L CW CF
    (profileMomentConstant (J + (volume : Measure ℝ).integrablePower)
      L H CW CF) A J
    hWc hWs hFs hR hm hm1 hH ha hL hCW hCF
    (profileMomentConstant_nonneg _ L H CW CF hL hCW hCF)
    hWderiv hwindow hFdecay
  intro j hj
  exact profileMomentConstant_dominates _ j L H CW CF hL hCW hCF hj
end OAI.FourierBridge
