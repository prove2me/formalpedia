-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.norm_taylor_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:13:32.59592+00:00
-- url     : https://prove2.me/submissions/8c63ae76-3c4d-4c9a-a17c-5889473e98d1

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
import Theorems.Thm_GroundTheory_Global_Quadratic_hasDerivAt_add_cpow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution (n : ℕ) (s : ℂ) {a b M : ℝ}
    (hpos : ∀ t ∈ uIcc a b, 0 < (n : ℝ) + t)
    (hM : ∀ t ∈ uIcc a b, ‖s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2)‖ ≤ M) :
    ‖(((n : ℝ) + b : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + a : ℝ) : ℂ) ^ (-s) -
        (-s * (((n : ℝ) + a : ℝ) : ℂ) ^ (-s - 1)) * ((b - a : ℝ) : ℂ)‖ ≤ M * |b - a| ^ 2 := by
  have hconv : Convex ℝ (uIcc a b) := convex_uIcc a b
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hb : b ∈ uIcc a b := right_mem_uIcc

  set ψ : ℝ → ℂ := fun t ↦ -s * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 1) with hψ
  have hψd : ∀ t ∈ uIcc a b, HasDerivWithinAt ψ (s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2))
      (uIcc a b) t := by
    intro t ht
    have h := (hasDerivAt_add_cpow n (hpos t ht) (-s - 1)).const_mul (-s)
    have he : -s * ((-s - 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 1 - 1)) =
        s * (s + 1) * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 2) := by
      rw [show -s - 1 - 1 = -s - 2 by ring]
      ring
    rw [he] at h
    exact h.hasDerivWithinAt
  have hψb : ∀ t ∈ uIcc a b, ‖ψ t - ψ a‖ ≤ M * |b - a| := by
    intro t ht
    have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hψd hM ha ht
    refine h.trans (mul_le_mul_of_nonneg_left ?_ ((norm_nonneg _).trans (hM a ha)))
    rw [Real.norm_eq_abs]
    exact abs_sub_left_of_mem_uIcc ht

  set R : ℝ → ℂ := fun t ↦ (((n : ℝ) + t : ℝ) : ℂ) ^ (-s) - (((n : ℝ) + a : ℝ) : ℂ) ^ (-s) -
    ψ a * ((t - a : ℝ) : ℂ) with hR
  have hRd : ∀ t ∈ uIcc a b, HasDerivWithinAt R (ψ t - ψ a) (uIcc a b) t := by
    intro t ht
    have h1 := hasDerivAt_add_cpow n (hpos t ht) (-s)
    have h2 : HasDerivAt (fun u : ℝ ↦ ψ a * ((u - a : ℝ) : ℂ)) (ψ a * 1) t := by
      have := ((hasDerivAt_id t).sub_const a).ofReal_comp.const_mul (ψ a)
      simpa using this
    have h3 := (h1.sub_const ((((n : ℝ) + a : ℝ) : ℂ) ^ (-s))).sub h2
    rw [mul_one] at h3
    have he : -s * (((n : ℝ) + t : ℝ) : ℂ) ^ (-s - 1) = ψ t := rfl
    rw [he] at h3
    exact h3.hasDerivWithinAt
  have h := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hRd hψb ha hb
  have hRa : R a = 0 := by simp [hR]
  rw [hRa, sub_zero, Real.norm_eq_abs, mul_assoc, ← pow_two] at h
  exact h
end GroundTheory.Global.Quadratic
