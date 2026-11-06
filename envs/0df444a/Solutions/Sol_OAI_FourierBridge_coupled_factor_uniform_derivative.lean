-- Prove2me | solution 1 for OAI.FourierBridge.coupled_factor_uniform_derivative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:32:14.337147+00:00
-- url     : https://prove2.me/submissions/02a6f76c-6a12-4557-a854-9768fb4f50a1

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_coupled_factor_derivative_bound
import Theorems.Thm_OAI_FourierBridge_derivative_scale_absorption

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
    (F : ℝ → ℂ) (R a y m H CF : ℝ) (A n j : ℕ)
    (hF : ContDiff ℝ ∞ F)
    (hR : 0 ≤ R) (hm : 0 < m) (hm1 : m ≤ 1)
    (hH : 1 ≤ H) (ha : |a| ≤ H)
    (hexpLower : m ≤ Real.exp (a * y))
    (hexpUpper : Real.exp (a * y) ≤ H)
    (hj : j ≤ n) (hCF : 0 ≤ CF)
    (hFdecay : ∀ i ≤ n, ∀ u, 0 ≤ u →
      (1 + u) ^ (A + n) * ‖iteratedFDeriv ℝ i F u‖ ≤ CF) :
    m ^ (A + n) * (1 + R) ^ A *
      ‖iteratedFDeriv ℝ j (fun z : ℝ => F (R * Real.exp (a * z))) y‖ ≤
        (j.factorial : ℝ) * CF * (H ^ 2) ^ j := by
  have hcomp := coupled_factor_derivative_bound F R a y H CF A n j hF hR hH
    ha hexpUpper hj hCF hFdecay
  have hscale : 0 ≤ m ^ (A + n) * (1 + R) ^ A := by positivity
  have hlower : m * (1 + R) ≤ 1 + R * Real.exp (a * y) := by
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hexpLower)]
  exact (mul_le_mul_of_nonneg_left hcomp hscale).trans
    (derivative_scale_absorption R (R * Real.exp (a * y)) m H CF A n j
      hR hm (by linarith) hCF (by positivity) hlower hj)
end OAI.FourierBridge
