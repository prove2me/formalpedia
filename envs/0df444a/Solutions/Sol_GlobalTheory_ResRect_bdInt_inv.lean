-- Prove2me | solution 1 for GlobalTheory.ResRect.bdInt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:56:34.47989+00:00
-- url     : https://prove2.me/submissions/74d4e4d8-3e61-4a4c-a0f4-eb08195f87d4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_BdIntEqZeroOfPrimitive
import Theorems.Thm_GlobalTheory_ResRect_ftc_hor
import Theorems.Thm_GlobalTheory_ResRect_ftc_ver

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.ResRect
namespace GlobalTheory.ResRect
theorem _root_.solution {a b c d : ℝ} {p : ℂ} (h1 : a < p.re) (h2 : p.re < b) (h3 : c < p.im)
    (h4 : p.im < d) (k : ℂ) : bdInt a b c d (fun s => k / (s - p)) = 2 * Real.pi * I * k := by
  have hc : ∀ B : Set ℂ, (∀ s ∈ B, s - p ≠ 0) → ContinuousOn (fun s => k / (s - p)) B :=
    fun B hB => ContinuousOn.div (by fun_prop) (by fun_prop) hB
  have hc1 := hc {s | s - p ∈ slitPlane} fun s hs => slitPlane_ne_zero hs
  have hc2 := hc {s | -(s - p) ∈ slitPlane} fun s hs => neg_ne_zero.1 (slitPlane_ne_zero hs)
  have hd1 : ∀ s ∈ {s | s - p ∈ slitPlane},
      HasDerivAt (fun s => k * log (s - p)) (k / (s - p)) s := fun s hs => by
    have := (((hasDerivAt_id s).sub_const p).clog hs).const_mul k
    refine this.congr_deriv ?_
    simp only [id]
    ring
  have hd2 : ∀ s ∈ {s | -(s - p) ∈ slitPlane},
      HasDerivAt (fun s => k * log (-(s - p))) (k / (s - p)) s := fun s hs => by
    have := (((hasDerivAt_id s).sub_const p).neg.clog hs).const_mul k
    refine this.congr_deriv ?_
    simp only [id, Pi.neg_apply, neg_div_neg_eq]
    ring
  simp only [bdInt]
  rw [ftc_hor hc1 hd1 (c := c) fun x _ => Or.inr (by simp; linarith),
    ftc_hor hc1 hd1 (c := d) fun x _ => Or.inr (by simp; linarith),
    ftc_ver hc1 hd1 (a := b) fun x _ => Or.inl (by simp; linarith),
    ftc_ver hc2 hd2 (a := a) fun x _ => Or.inl (by simp; linarith)]
  have e1 : log (-((a : ℂ) + d * I - p)) = log ((a : ℂ) + d * I - p) - Real.pi * I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos (by simp; linarith)]
    push_cast; ring
  have e2 : log (-((a : ℂ) + c * I - p)) = log ((a : ℂ) + c * I - p) + Real.pi * I := by
    rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg (by simp; linarith)]
    push_cast; ring
  rw [e1, e2]
  ring
end GlobalTheory.ResRect
