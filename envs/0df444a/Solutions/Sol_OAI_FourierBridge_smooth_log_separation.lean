-- Prove2me | solution 1 for OAI.FourierBridge.smooth_log_separation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:50.63842+00:00
-- url     : https://prove2.me/submissions/fb8222b5-da26-4d46-aaa5-ed6c4df8956d

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_schwartz_log_inversion
import Theorems.Thm_OAI_FourierBridge_logProfile_apply

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
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a y : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    W y * F (R * Real.exp (a * y)) =
      ∫ t : ℝ, Complex.exp ((↑(2 * Real.pi * inner ℝ t y) * Complex.I)) *
        (𝓕 (logProfile W F R a hWc hWs hFs)) t := by
  rw [← logProfile_apply W F R a y hWc hWs hFs]
  exact schwartz_log_inversion _ _
end OAI.FourierBridge
