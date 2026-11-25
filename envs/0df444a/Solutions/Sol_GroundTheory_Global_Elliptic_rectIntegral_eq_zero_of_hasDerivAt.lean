-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_eq_zero_of_hasDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:07:21.196125+00:00
-- url     : https://prove2.me/submissions/aec9781a-f8e3-4588-a3eb-e9e0a9bee7bf

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_bottom_mem_rectBoundary
import Theorems.Thm_GroundTheory_Global_Elliptic_top_mem_rectBoundary
import Theorems.Thm_GroundTheory_Global_Elliptic_right_mem_rectBoundary
import Theorems.Thm_GroundTheory_Global_Elliptic_left_mem_rectBoundary
import Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_bottom
import Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_top
import Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_right
import Theorems.Thm_GroundTheory_Global_Elliptic_intervalIntegrable_left

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
variable {z w : ℂ}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution [CompleteSpace E] {F f : ℂ → E}
    (hF : ∀ u ∈ rectBoundary z w, HasDerivAt F (f u) u) (hf : ContinuousOn f (rectBoundary z w)) :
    rectIntegral f z w = 0 := by
  have hh : ∀ c : ℝ, ∀ x : ℝ, (x : ℂ) + c * I ∈ rectBoundary z w →
      HasDerivAt (fun x : ℝ ↦ F (x + c * I)) (f (x + c * I)) x := by
    intro c x hx
    have h1 : HasDerivAt (fun y : ℝ ↦ (y : ℂ) + c * I) 1 x := by
      simpa using (hasDerivAt_id' x).ofReal_comp.add_const ((c : ℂ) * I)
    have h2 := (hF _ hx).scomp x h1
    rw [one_smul] at h2
    exact h2
  have hv : ∀ c : ℝ, ∀ y : ℝ, (c : ℂ) + y * I ∈ rectBoundary z w →
      HasDerivAt (fun y : ℝ ↦ F (c + y * I)) (I • f (c + y * I)) y := by
    intro c y hy
    have h1 : HasDerivAt (fun y : ℝ ↦ (c : ℂ) + y * I) I y := by
      simpa using ((hasDerivAt_id' y).ofReal_comp.mul_const I).const_add (c : ℂ)
    exact (hF _ hy).scomp y h1
  have hb : ∫ x : ℝ in z.re..w.re, f (x + z.im * I) =
      F (w.re + z.im * I) - F (z.re + z.im * I) :=
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hh _ x (bottom_mem_rectBoundary hx))
      (intervalIntegrable_bottom hf)
  have ht : ∫ x : ℝ in z.re..w.re, f (x + w.im * I) =
      F (w.re + w.im * I) - F (z.re + w.im * I) :=
    integral_eq_sub_of_hasDerivAt (fun x hx ↦ hh _ x (top_mem_rectBoundary hx))
      (intervalIntegrable_top hf)
  have hr : I • ∫ y : ℝ in z.im..w.im, f (w.re + y * I) =
      F (w.re + w.im * I) - F (w.re + z.im * I) := by
    rw [← intervalIntegral.integral_smul]
    exact integral_eq_sub_of_hasDerivAt (fun y hy ↦ hv _ y (right_mem_rectBoundary hy))
      ((intervalIntegrable_right hf).smul I)
  have hl : I • ∫ y : ℝ in z.im..w.im, f (z.re + y * I) =
      F (z.re + w.im * I) - F (z.re + z.im * I) := by
    rw [← intervalIntegral.integral_smul]
    exact integral_eq_sub_of_hasDerivAt (fun y hy ↦ hv _ y (left_mem_rectBoundary hy))
      ((intervalIntegrable_left hf).smul I)
  rw [rectIntegral, hb, ht, hr, hl]
  abel
end GroundTheory.Global.Elliptic
