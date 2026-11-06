-- Prove2me | solution 1 for OAI.FourierBridge.logProfile_coefficient_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:04:26.758293+00:00
-- url     : https://prove2.me/submissions/e7437b95-3ee0-4b09-8d99-8b803b4b3bca

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
    (W F : ℝ → ℂ) (R a : ℝ) (J : ℕ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    Integrable (fun t : ℝ => ‖t‖ ^ J *
      ‖(𝓕 (logProfile W F R a hWc hWs hFs)) t‖) volume :=
  (𝓕 (logProfile W F R a hWc hWs hFs)).integrable_pow_mul volume J
end OAI.FourierBridge
