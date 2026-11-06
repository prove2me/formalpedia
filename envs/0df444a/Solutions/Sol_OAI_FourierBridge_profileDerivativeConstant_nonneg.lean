-- Prove2me | solution 1 for OAI.FourierBridge.profileDerivativeConstant_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:14:34.493211+00:00
-- url     : https://prove2.me/submissions/1cb83375-29fd-4423-a79d-3e16a8d30450

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
theorem _root_.solution (n : ℕ) (H CW CF : ℝ)
    (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) :
    0 ≤ profileDerivativeConstant n H CW CF := by
  unfold profileDerivativeConstant
  apply Finset.sum_nonneg
  intro i hi
  positivity
end OAI.FourierBridge
