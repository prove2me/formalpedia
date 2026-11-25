-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_eq_zero_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:21.854203+00:00
-- url     : https://prove2.me/submissions/69e88fff-faea-4bed-aec1-4ca52864ab4a

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Set Real MeasureTheory Filter Topology intervalIntegral
open scoped Interval
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {g : ℂ → E} {τ : ℂ} (h1 : ∀ u, g (u + 1) = g u)
    (hτ : ∀ u, g (u + τ) = g u) (a : ℂ) : rectIntegral g a (a + 1 + τ.im * I) = 0 := by
  have hre : (a + 1 + τ.im * I).re = a.re + 1 := by simp
  have him : (a + 1 + τ.im * I).im = a.im + τ.im := by simp
  have hv : ∫ y : ℝ in a.im..a.im + τ.im, g (((a.re + 1 : ℝ) : ℂ) + y * I) =
      ∫ y : ℝ in a.im..a.im + τ.im, g ((a.re : ℂ) + y * I) := by
    congr 1
    ext y
    rw [← h1 ((a.re : ℂ) + y * I)]
    congr 1
    push_cast
    ring
  have hh : ∫ x : ℝ in a.re..a.re + 1, g ((x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I) =
      ∫ x : ℝ in a.re..a.re + 1, g ((x : ℂ) + a.im * I) := by
    have e : ∀ x : ℝ, g ((x : ℂ) + ((a.im + τ.im : ℝ) : ℂ) * I) =
        g (((x - τ.re : ℝ) : ℂ) + a.im * I) := by
      intro x
      rw [← hτ (((x - τ.re : ℝ) : ℂ) + a.im * I)]
      congr 1
      apply Complex.ext <;> simp
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right (fun t : ℝ ↦ g ((t : ℂ) + a.im * I)) τ.re
      (a := a.re) (b := a.re + 1)
    rw [this]
    have hper : Function.Periodic (fun t : ℝ ↦ g ((t : ℂ) + a.im * I)) 1 := by
      intro t
      beta_reduce
      rw [← h1 ((t : ℂ) + a.im * I)]
      congr 1
      push_cast
      ring
    rw [show a.re + 1 - τ.re = a.re - τ.re + 1 by ring]
    exact hper.intervalIntegral_add_eq (a.re - τ.re) a.re
  unfold rectIntegral
  rw [hre, him, hv, hh]
  abel
end GroundTheory.Global.Elliptic
