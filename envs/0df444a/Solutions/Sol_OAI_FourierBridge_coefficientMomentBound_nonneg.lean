-- Prove2me | solution 1 for OAI.FourierBridge.coefficientMomentBound_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:30:11.772201+00:00
-- url     : https://prove2.me/submissions/17f0e1a3-d730-4197-857a-8ee4b292e082

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
theorem _root_.solution (J : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    0 ≤ coefficientMomentBound J C := by
  unfold coefficientMomentBound
  positivity
end OAI.FourierBridge
