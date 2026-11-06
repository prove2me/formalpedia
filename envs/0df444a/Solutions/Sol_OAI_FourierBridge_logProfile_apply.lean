-- Prove2me | solution 1 for OAI.FourierBridge.logProfile_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:14:14.093027+00:00
-- url     : https://prove2.me/submissions/3f48c60e-0ac3-4ed3-af89-3e7e5d73297c

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
    (W : ℝ → ℂ) (F : ℝ → ℂ) (R a y : ℝ)
    (hWc : HasCompactSupport W)
    (hWs : ContDiff ℝ ∞ W)
    (hFs : ContDiff ℝ ∞ F) :
    logProfile W F R a hWc hWs hFs y = W y * F (R * Real.exp (a * y)) := rfl
end OAI.FourierBridge
