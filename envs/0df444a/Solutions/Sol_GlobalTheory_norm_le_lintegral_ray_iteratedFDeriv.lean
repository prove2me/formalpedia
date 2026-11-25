-- Prove2me | solution 1 for GlobalTheory.norm_le_lintegral_ray_iteratedFDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:03:04.917586+00:00
-- url     : https://prove2.me/submissions/98ed6584-f5b3-42e3-8bd5-bf3a41f26178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralTaylorTailIteratedDerivStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormLeLintegralRayIteratedFDeriv
import Theorems.Thm_GlobalTheory_T_norm_le_lintegral_taylor_tail_iteratedDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set Module
open scoped ENNReal
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] (G : E → F) (m : ℕ) (x v : E)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hdec : ∀ j ≤ m, Tendsto (fun t : ℝ => iteratedFDeriv ℝ j G (x + t • v)) atTop (𝓝 0)) :
    ENNReal.ofReal ‖G x‖ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m / (m.factorial : ℝ) *
      (‖v‖ ^ (m + 1) * ‖iteratedFDeriv ℝ (m + 1) G (x + t • v)‖)) := by
  set L : ℝ →L[ℝ] E := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) v with hL
  have hLt : ∀ t : ℝ, L t = t • v := fun t => by simp [hL]
  set Gx : E → F := fun z => G (x + z) with hGx
  have hGx' : ContDiff ℝ (⊤ : ℕ∞) Gx := hG.comp (contDiff_const.add contDiff_id)
  set h : ℝ → F := Gx ∘ L with hh
  have hhs : ContDiff ℝ (⊤ : ℕ∞) h := hGx'.comp L.contDiff
  have key : ∀ (j : ℕ) (t : ℝ),
      iteratedDeriv j h t = iteratedFDeriv ℝ j G (x + t • v) (fun _ => v) := by
    intro j t
    rw [iteratedDeriv_eq_iteratedFDeriv, hh,
      L.iteratedFDeriv_comp_right hGx' t (by exact_mod_cast le_top),
      ContinuousMultilinearMap.compContinuousLinearMap_apply, hGx,
      iteratedFDeriv_comp_add_left, hLt]
    simp [hLt]
  have bound : ∀ (j : ℕ) (t : ℝ),
      ‖iteratedDeriv j h t‖ ≤ ‖iteratedFDeriv ℝ j G (x + t • v)‖ * ‖v‖ ^ j := by
    intro j t
    rw [key]
    refine ((iteratedFDeriv ℝ j G (x + t • v)).le_opNorm _).trans (le_of_eq ?_)
    simp [Finset.prod_const]
  have hdec' : ∀ j ≤ m, Tendsto (iteratedDeriv j h) atTop (𝓝 0) := by
    intro j hj
    refine squeeze_zero_norm (fun t => bound j t) ?_
    have := ((hdec j hj).norm).mul_const (‖v‖ ^ j)
    simpa using this
  have h0 : h 0 = G x := by simp [hh, hGx, hLt]
  have main := GlobalTheory.T.norm_le_lintegral_taylor_tail_iteratedDeriv h m hhs hdec'
  rw [h0] at main
  refine main.trans (lintegral_mono_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ha : 0 ≤ t ^ m / (m.factorial : ℝ) := by
    have : (0:ℝ) < t := ht
    positivity
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul ha]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ ha)
  rw [mul_comm]
  exact bound (m + 1) t
end GlobalTheory
