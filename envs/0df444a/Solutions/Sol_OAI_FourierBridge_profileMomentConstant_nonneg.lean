-- Prove2me | solution 1 for OAI.FourierBridge.profileMomentConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:23.029942+00:00
-- url     : https://prove2.me/submissions/0004df0b-6962-4134-b0c5-b9dc228eaf3b

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Theorems.Thm_OAI_FourierBridge_profileDerivativeConstant_nonneg

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
theorem _root_.solution (K : ℕ) (L H CW CF : ℝ)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ profileMomentConstant K L H CW CF := by
  unfold profileMomentConstant
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (by positivity)
    (profileDerivativeConstant_nonneg j H CW CF hCW hCF)
end OAI.FourierBridge
