-- Prove2me | solution 1 for GroundTheory.Automorphic.GL2Classical.integral_periodic_eq_of_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:48:49.956984+00:00
-- url     : https://prove2.me/submissions/3dca3b85-1fcd-4d91-9cdd-29b8a10a82fe

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2Classical_Periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory intervalIntegral Filter Topology Set
open UpperHalfPlane hiding I I_re I_im
open scoped Manifold Interval
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.GL2Classical
namespace GroundTheory.Automorphic.GL2Classical
theorem _root_.solution {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G {w | 0 < w.im}) {T : ℝ}
    (hper : ∀ w : ℂ, 0 < w.im → G (w + T) = G w) (x₀ : ℝ) {y₁ y₂ : ℝ} (hy₁ : 0 < y₁)
    (hy₂ : 0 < y₂) :
    ∫ x in x₀..x₀ + T, G (x + y₁ * I) = ∫ x in x₀..x₀ + T, G (x + y₂ * I) := by
  have hsub : [[x₀, x₀ + T]] ×ℂ [[y₁, y₂]] ⊆ {w : ℂ | 0 < w.im} := by
    intro w hw
    rw [mem_reProdIm] at hw
    have := hw.2
    rw [Set.mem_uIcc] at this
    show 0 < w.im
    rcases this with h | h
    · exact lt_of_lt_of_le hy₁ h.1
    · exact lt_of_lt_of_le hy₂ h.1
  have H := integral_boundary_rect_eq_zero_of_differentiableOn G (x₀ + y₁ * I)
    ((x₀ + T : ℝ) + y₂ * I) (by
      refine hG.mono (Set.Subset.trans ?_ hsub)
      simp)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add] at H
  have hv : ∫ y in y₁..y₂, G (((x₀ + T : ℝ) : ℂ) + y * I) = ∫ y in y₁..y₂, G ((x₀ : ℂ) + y * I) := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    have hy0 : 0 < y := by
      rw [Set.mem_uIcc] at hy
      rcases hy with h | h
      · exact lt_of_lt_of_le hy₁ h.1
      · exact lt_of_lt_of_le hy₂ h.1
    have := hper ((x₀ : ℂ) + y * I) (by simpa using hy0)
    rw [← this]
    congr 1
    push_cast
    ring
  rw [hv, add_sub_cancel_right, sub_eq_zero] at H
  exact H
end GroundTheory.Automorphic.GL2Classical
