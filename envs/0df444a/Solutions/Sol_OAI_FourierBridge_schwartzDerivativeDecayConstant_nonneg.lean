-- Prove2me | solution 1 for OAI.FourierBridge.schwartzDerivativeDecayConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:38.087724+00:00
-- url     : https://prove2.me/submissions/c270f1dc-be52-4ab4-ba3a-6e06e8e6a9ae

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
    (F : 𝓢(ℝ, ℂ)) (M K : ℕ) :
    0 ≤ schwartzDerivativeDecayConstant F M K := by
  unfold schwartzDerivativeDecayConstant
  positivity
end OAI.FourierBridge
