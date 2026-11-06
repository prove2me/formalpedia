-- Prove2me | solution 1 for OAI.FourierBridge.schwartz_log_inversion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:29:49.238127+00:00
-- url     : https://prove2.me/submissions/89c2f62f-120b-40b8-84b7-7192c73a0ea7

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
theorem _root_.solution (g : 𝓢(ℝ, ℂ)) (y : ℝ) :
    g y = ∫ t : ℝ,
      Complex.exp ((↑(2 * Real.pi * inner ℝ t y) * Complex.I)) * (𝓕 g) t := by
  have hinv : (𝓕⁻ (𝓕 g) : 𝓢(ℝ, ℂ)) = g := by simp
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f y) hinv
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at h
  simpa only [smul_eq_mul] using h.symm
end OAI.FourierBridge
