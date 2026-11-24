-- Prove2me | solution 1 for GlobalTheory.ContinuousHomDifferentiable.exists_integral_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:57:26.696394+00:00
-- url     : https://prove2.me/submissions/65952351-8188-4bae-8a77-5dadf499f7a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ContinuousHomDifferentiable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ContinuousHomDifferentiable
open intervalIntegral
namespace GlobalTheory.ContinuousHomDifferentiable
theorem _root_.solution (χ : ℝ → ℂ) (hc : Continuous χ) (h0 : χ 0 = 1) :
    ∃ δ : ℝ, (∫ x in (0:ℝ)..δ, χ x) ≠ 0 := by
  by_contra h
  push_neg at h
  have h1 : HasDerivAt (fun u => ∫ x in (0:ℝ)..u, χ x) (χ 0) 0 :=
    (hc.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hfun : (fun u => ∫ x in (0:ℝ)..u, χ x) = fun _ => (0:ℂ) := funext h
  rw [hfun] at h1
  have h2 : HasDerivAt (fun _ : ℝ => (0:ℂ)) 0 0 := hasDerivAt_const _ _
  have := h1.unique h2
  rw [h0] at this
  exact one_ne_zero this
end GlobalTheory.ContinuousHomDifferentiable
