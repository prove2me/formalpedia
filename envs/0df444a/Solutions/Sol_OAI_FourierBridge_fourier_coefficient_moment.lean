-- Prove2me | solution 1 for OAI.FourierBridge.fourier_coefficient_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:14:23.290215+00:00
-- url     : https://prove2.me/submissions/3e7bf5e3-fcb8-4a70-9ec5-db3af007461d

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
theorem _root_.solution (g : 𝓢(ℝ, ℂ)) (J : ℕ) :
    ∫ t : ℝ, ‖t‖ ^ J * ‖(𝓕 g) t‖ ≤
      (2 ^ (volume : Measure ℝ).integrablePower *
        ∫ t : ℝ, (1 + ‖t‖) ^ (-(volume : Measure ℝ).integrablePower : ℝ)) *
      ((SchwartzMap.seminorm ℝ 0 0) (𝓕 g) +
        (SchwartzMap.seminorm ℝ (J + (volume : Measure ℝ).integrablePower) 0) (𝓕 g)) := by
  simpa using SchwartzMap.integral_pow_mul_iteratedFDeriv_le ℝ volume (𝓕 g) J 0
end OAI.FourierBridge
