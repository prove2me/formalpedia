-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.rectIntegral_sub_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:19:00.53394+00:00
-- url     : https://prove2.me/submissions/de56fb2b-3062-41a7-a3ff-433c8a6cf336

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_RectangleIntegral
import Theorems.Thm_GroundTheory_Global_Elliptic_integral_inv_ofReal_add_mul_I
import Theorems.Thm_GroundTheory_Global_Elliptic_invPrimitive_rect_sum

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
theorem _root_.solution {z w p : ℂ} (h1 : z.re < p.re) (h2 : p.re < w.re) (h3 : z.im < p.im)
    (h4 : p.im < w.im) : rectIntegral (fun u ↦ (u - p)⁻¹) z w = 2 * π * I := by
  have horiz : ∀ c : ℝ, c - p.im ≠ 0 → ∫ x : ℝ in z.re..w.re, ((x : ℂ) + c * I - p)⁻¹ =
      invPrimitive (c - p.im) (w.re - p.re) - invPrimitive (c - p.im) (z.re - p.re) := by
    intro c hc
    have e : ∀ x : ℝ, ((x : ℂ) + c * I - p) = ((x - p.re : ℝ) : ℂ) + ((c - p.im : ℝ) : ℂ) * I := by
      intro x; apply Complex.ext <;> simp
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ ↦ ((t : ℂ) + ((c - p.im : ℝ) : ℂ) * I)⁻¹) p.re (a := z.re) (b := w.re)
    rw [this]
    exact integral_inv_ofReal_add_mul_I hc _ _
  have vert : ∀ c : ℝ, -(c - p.re) ≠ 0 → I • ∫ y : ℝ in z.im..w.im, ((c : ℂ) + y * I - p)⁻¹ =
      invPrimitive (-(c - p.re)) (w.im - p.im) - invPrimitive (-(c - p.re)) (z.im - p.im) := by
    intro c hc
    rw [← intervalIntegral.integral_smul]
    have e : ∀ y : ℝ, I • ((c : ℂ) + y * I - p)⁻¹ =
        (((y - p.im : ℝ) : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I)⁻¹ := by
      intro y
      have hX : (c : ℂ) + y * I - p = I * (((y - p.im : ℝ) : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I) := by
        apply Complex.ext <;> simp
      rw [smul_eq_mul, hX, mul_inv, ← mul_assoc, mul_inv_cancel₀ I_ne_zero, one_mul]
    simp_rw [e]
    have := intervalIntegral.integral_comp_sub_right
      (fun t : ℝ ↦ ((t : ℂ) + ((-(c - p.re) : ℝ) : ℂ) * I)⁻¹) p.im (a := z.im) (b := w.im)
    rw [this]
    exact integral_inv_ofReal_add_mul_I hc _ _
  unfold rectIntegral
  beta_reduce
  rw [horiz _ (by linarith), horiz _ (by linarith), vert _ (by linarith), vert _ (by linarith)]
  exact invPrimitive_rect_sum (by linarith) (by linarith) (by linarith) (by linarith)
end GroundTheory.Global.Elliptic
