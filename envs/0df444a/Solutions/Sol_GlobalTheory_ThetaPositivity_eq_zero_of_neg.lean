-- Prove2me | solution 1 for GlobalTheory.ThetaPositivity.eq_zero_of_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:58:04.595411+00:00
-- url     : https://prove2.me/submissions/f5a4302d-887c-46d5-bf2d-266c8f102ab5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ReFormPosOfThetaNeZero
import Theorems.Thm_GlobalTheory_ThetaPositivity_form_add_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.ThetaPositivity
variable {g : ℕ}
open Complex Matrix Filter Topology in
open scoped BigOperators Real in
variable {g : ℕ} in
private lemma re_form_add_smul_of_isHermitian {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) (t : ℂ) :
    ((z + t • w) ⬝ᵥ Hm.mulVec (star (z + t • w))).re =
      (z ⬝ᵥ Hm.mulVec (star z)).re + 2 * (star t * (z ⬝ᵥ Hm.mulVec (star w))).re
        + Complex.normSq t * (w ⬝ᵥ Hm.mulVec (star w)).re := by
  rw [_root_.GlobalTheory.ThetaPositivity.form_add_self hH]
  have h1 : z ⬝ᵥ Hm.mulVec (star (t • w)) = star t * (z ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  have h2 : (t • w) ⬝ᵥ Hm.mulVec (star (t • w)) =
      (Complex.normSq t : ℂ) * (w ⬝ᵥ Hm.mulVec (star w)) := by
    rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, mul_comm (star t), Complex.star_def, Complex.mul_conj]
  rw [h1, h2, Complex.re_ofReal_mul]
end GlobalTheory.ThetaPositivity
end

set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.ThetaPositivity
variable {g : ℕ}
open Complex Matrix Filter Topology
open scoped BigOperators Real
variable {g : ℕ}
namespace GlobalTheory.ThetaPositivity
namespace _root_.GlobalTheory.ThetaPositivity
theorem _root_.solution {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    {θ : (Fin g → ℂ) → ℂ} (hθ : Differentiable ℂ θ) {C : ℝ}
    (hC : ∀ z, ‖θ z‖ ≤ C * Real.exp (Real.pi / 2 * (z ⬝ᵥ Hm.mulVec (star z)).re))
    {w : Fin g → ℂ} (hw : (w ⬝ᵥ Hm.mulVec (star w)).re < 0) : θ = 0 := by
  funext z
  have hC0 : 0 ≤ C := by
    have h := hC 0
    have hp := Real.exp_pos (Real.pi / 2 * ((0 : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star 0)).re)
    nlinarith [norm_nonneg (θ 0)]
  set a := -(w ⬝ᵥ Hm.mulVec (star w)).re with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  set A := (z ⬝ᵥ Hm.mulVec (star z)).re with hA
  set B := ‖z ⬝ᵥ Hm.mulVec (star w)‖ with hB
  set f : ℂ → ℂ := fun t => θ (z + t • w) with hfdef
  have hf : Differentiable ℂ f :=
    hθ.comp ((differentiable_const _).add (differentiable_id.smul_const w))
  have hbound : ∀ t, ‖f t‖ ≤ C * Real.exp (Real.pi / 2 * (A + 2 * B * ‖t‖ - a * ‖t‖ ^ 2)) := by
    intro t
    refine (hC _).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [re_form_add_smul_of_isHermitian hH, Complex.normSq_eq_norm_sq]
    have h : (star t * (z ⬝ᵥ Hm.mulVec (star w))).re ≤ ‖t‖ * B := by
      refine (Complex.re_le_norm _).trans ?_
      rw [norm_mul, norm_star]
    nlinarith
  have hlim : Tendsto (fun r : ℝ => C * Real.exp (Real.pi / 2 * (A + 2 * B * r - a * r ^ 2)))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun r : ℝ => (A + 2 * B ^ 2 / a) + (-(a / 2)) * r ^ 2) atTop atBot :=
      tendsto_atBot_add_const_left _ _
        ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (by linarith))
    have h1 : Tendsto (fun r : ℝ => A + 2 * B * r - a * r ^ 2) atTop atBot := by
      refine tendsto_atBot_mono (fun r => ?_) h2
      have key : 2 * B ^ 2 / a + a / 2 * r ^ 2 - 2 * B * r = (a * r - 2 * B) ^ 2 / (2 * a) := by
        field_simp
        ring
      have : 0 ≤ (a * r - 2 * B) ^ 2 / (2 * a) := by positivity
      nlinarith
    have h3 := Real.tendsto_exp_atBot.comp (h1.const_mul_atBot (by positivity : 0 < Real.pi / 2))
    simpa using h3.const_mul C
  have hf0 : Tendsto f (cocompact ℂ) (𝓝 0) :=
    squeeze_zero_norm hbound (hlim.comp tendsto_norm_cocompact_atTop)
  have := hf.apply_eq_of_tendsto_cocompact 0 hf0
  simpa [hfdef] using this
end _root_.GlobalTheory.ThetaPositivity
end GlobalTheory.ThetaPositivity
