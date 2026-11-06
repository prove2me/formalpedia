-- Prove2me | solution 1 for OAI.FourierBridge.profileMomentConstant_dominates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:15:23.678714+00:00
-- url     : https://prove2.me/submissions/bb367caf-78ba-437a-a01b-cf94c53328b6

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
theorem _root_.solution (K j : ℕ) (L H CW CF : ℝ)
    (hL : 0 ≤ L) (hCW : 0 ≤ CW) (hCF : 0 ≤ CF) (hj : j ≤ K) :
    (1 + L ^ (volume : Measure ℝ).integrablePower) *
      profileDerivativeConstant j H CW CF ≤
      profileMomentConstant K L H CW CF := by
  unfold profileMomentConstant
  apply Finset.single_le_sum
    (f := fun i : ℕ =>
      (1 + L ^ (volume : Measure ℝ).integrablePower) *
        profileDerivativeConstant i H CW CF)
    (a := j)
  · intro i hi
    exact mul_nonneg (by positivity)
      (profileDerivativeConstant_nonneg i H CW CF hCW hCF)
  · exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj)
end OAI.FourierBridge
