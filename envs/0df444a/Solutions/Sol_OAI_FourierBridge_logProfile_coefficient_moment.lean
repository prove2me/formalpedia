-- Prove2me | solution 1 for OAI.FourierBridge.logProfile_coefficient_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:27.611281+00:00
-- url     : https://prove2.me/submissions/0e4d7d12-0bce-454c-85fd-bd51540ee9ba

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_fourier_coefficient_moment

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
    (W F : ℝ → ℂ) (R a : ℝ) (J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0)
          (𝓕 (logProfile W F R a hWc hWs hFs)) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0)
          (𝓕 (logProfile W F R a hWc hWs hFs))) :=
  fourier_coefficient_moment _ J
end OAI.FourierBridge
