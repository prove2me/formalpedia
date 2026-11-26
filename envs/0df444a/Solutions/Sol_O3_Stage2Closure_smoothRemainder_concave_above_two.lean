-- Prove2me | solution 1 for O3.Stage2Closure.smoothRemainder_concave_above_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:25.265032+00:00
-- url     : https://prove2.me/submissions/a296024b-ffb8-4b42-8c04-5c0e524f6bad

import Definitions.Def_O3_Stage2RouteA
import Definitions.Def_O3_Stage2RouteB
import Mathlib.Analysis.Convex.Deriv
import Definitions.Def_O3_Stage2BelowGeometry
import Theorems.Thm_O3_Stage2Closure_hasDerivAt_smoothRemainder
import Theorems.Thm_O3_Stage2Closure_exists_hasDerivAt_smoothRemainderDeriv_nonpos
import Theorems.Thm_O3_Stage2RouteD_dualityMap_zero
import Theorems.Thm_O3_lpNorm_neg
import Theorems.Thm_O3_lpNorm_zero
import Theorems.Thm_O3_lpPower_neg
import Theorems.Thm_O3_lpPower_zero
import Theorems.Thm_O3_pairing_neg_left
import Theorems.Thm_O3_pairing_neg_right
attribute [local simp] O3.Stage2RouteD.dualityMap_zero
attribute [local simp] O3.lpNorm_neg
attribute [local simp] O3.lpNorm_zero
attribute [local simp] O3.lpPower_neg
attribute [local simp] O3.lpPower_zero
attribute [local simp] O3.pairing_neg_left
attribute [local simp] O3.pairing_neg_right



set_option autoImplicit true
open O3
open O3.Stage2Closure
open scoped BigOperators
open Stage2RouteA Stage2RouteB
namespace O3.Stage2Closure
theorem _root_.solution {q : ℝ} (hq : 2 < q) {d : ℕ}
    (u h : Point d) : ConcaveOn ℝ Set.univ (smoothRemainder q u h) := by
  have hGdiff : Differentiable ℝ (smoothRemainderDeriv q u h) := by
    intro t
    obtain ⟨w, hw, _⟩ := exists_hasDerivAt_smoothRemainderDeriv_nonpos hq u h t
    exact hw.differentiableAt
  have hGnonpos : ∀ t, deriv (smoothRemainderDeriv q u h) t ≤ 0 := by
    intro t
    obtain ⟨w, hw, hw0⟩ := exists_hasDerivAt_smoothRemainderDeriv_nonpos hq u h t
    rw [hw.deriv]
    exact hw0
  have hGanti : Antitone (smoothRemainderDeriv q u h) :=
    antitone_of_deriv_nonpos hGdiff hGnonpos
  have hFdiff : Differentiable ℝ (smoothRemainder q u h) :=
    fun t ↦ (hasDerivAt_smoothRemainder (by linarith : 1 < q) u h t).differentiableAt
  have hFderiv : deriv (smoothRemainder q u h) = smoothRemainderDeriv q u h := by
    funext t
    exact (hasDerivAt_smoothRemainder (by linarith : 1 < q) u h t).deriv
  have hanti : Antitone (deriv (smoothRemainder q u h)) := by
    simpa only [hFderiv] using hGanti
  exact hanti.concaveOn_univ_of_deriv hFdiff
end O3.Stage2Closure
