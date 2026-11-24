-- Prove2me | solution 1 for GlobalTheory.GLFirstColumn.haar_first_column
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:05:06.151789+00:00
-- url     : https://prove2.me/submissions/5c974996-027d-4364-ba0c-7674b94b2278

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MeasurePreservingCons
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_left
import Theorems.Thm_GlobalTheory_GLFirstColumn_of_mulM
import Theorems.Thm_GlobalTheory_GLFirstColumn_of_invM
import Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_mulM
import Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_invM
import Theorems.Thm_GlobalTheory_GLFirstColumn_measurable_wt
import Theorems.Thm_GlobalTheory_GLFirstColumn_wt_mul
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_inv
import Theorems.Thm_GlobalTheory_GLFirstColumn_exists_section
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_first_col
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_first_row
import Theorems.Thm_GlobalTheory_GLFirstColumn_lintegral_blk_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped ENNReal
open GlobalTheory GlobalTheory.GLFirstColumn
namespace GlobalTheory.GLFirstColumn
theorem _root_.solution : ∀ (k : ℕ), 1 ≤ k → ∃ s : (Fin (k + 1) → ℂ) → Fin (k + 1) → Fin (k + 1) → ℂ, Measurable s ∧ (∀ x, x ≠ 0 → (Matrix.of (s x)).det = 1 ∧ ∀ a, s x a 0 = x a) ∧ ∀ φ : (Fin (k + 1) → Fin (k + 1) → ℂ) → ENNReal, Measurable φ → ∫⁻ g, φ g * ENNReal.ofReal ((‖(Matrix.of g).det‖ ^ 2)⁻¹ ^ (k + 1)) = ∫⁻ x : Fin (k + 1) → ℂ, ∫⁻ h : Fin k → Fin k → ℂ, ∫⁻ T : Fin k → ℂ, φ (fun a b => (Matrix.of (Fin.cons (Fin.cons 1 (T ᵥ* Matrix.of h)) (fun a' => Fin.cons 0 (h a')) : Fin (k + 1) → Fin (k + 1) → ℂ) * (Matrix.of (s x))⁻¹) a b) * ENNReal.ofReal (‖(Matrix.of h).det‖ ^ 2 * (‖(Matrix.of h).det‖ ^ 2)⁻¹ ^ k) := by
  intro k hk
  obtain ⟨s, hsm, hs⟩ := exists_section k hk
  refine ⟨s, hsm, hs, fun φ hφ => ?_⟩
  have hF : Measurable fun y => φ (invM y) * wt y := (hφ.comp measurable_invM).mul measurable_wt
  refine (lintegral_inv φ hφ).symm.trans ((lintegral_first_col _ hF).trans ?_)
  have hae : ∀ᵐ x : Fin (k + 1) → ℂ, x ≠ 0 := by
    rw [ae_iff]
    simp
  refine lintegral_congr_ae (hae.mono fun x hx => ?_)
  obtain ⟨hd, h0⟩ := hs x hx
  have hc : Measurable fun (Y : Fin (k + 1) → Fin k → ℂ) (a : Fin (k + 1)) =>
      (Fin.cons (x a) (Y a) : Fin (k + 1) → ℂ) := by
    refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun b => ?_
    refine Fin.cases ?_ (fun b => ?_) b
    · exact measurable_const
    · exact (measurable_pi_apply b).comp (measurable_pi_apply a)
  have hl : Measurable fun (Y : Fin (k + 1) → Fin k → ℂ) (a : Fin (k + 1)) (b : Fin k) =>
      (Matrix.of (s x) * Matrix.of Y) a b := by
    refine Continuous.measurable (continuous_pi fun a => continuous_pi fun b => ?_)
    simp only [Matrix.mul_apply, of_apply]
    fun_prop
  have h1 := lintegral_left (Matrix.of (s x)) (hd ▸ one_ne_zero) _ (hF.comp hc)
  have h2 := lintegral_first_row _ ((hF.comp hc).comp hl)
  have h3 := lintegral_blk_inv (fun g => φ (mulM g (invM (s x))))
    (hφ.comp (measurable_mulM measurable_id' measurable_const))
  rw [hd, norm_one, one_pow, one_pow, ENNReal.ofReal_one, one_mul] at h1
  refine h1.trans (h2.trans (Eq.trans ?_ h3))
  refine lintegral_congr fun m => lintegral_congr fun r => ?_
  have e : (fun a => (Fin.cons (x a) fun b => (Matrix.of (s x) *
      Matrix.of (Fin.cons r m : Fin (k + 1) → Fin k → ℂ)) a b : Fin (k + 1) → ℂ)) =
      mulM (s x) (blk r m) := by
    funext a b
    refine Fin.cases ?_ (fun b => ?_) b
    · simp [mulM, blk, Matrix.mul_apply, Fin.sum_univ_succ, h0]
    · simp [mulM, blk, Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [Function.comp_apply]
  rw [e, wt_mul]
  have hw : wt (s x) = 1 := by simp [wt, hd]
  have hi : invM (mulM (s x) (blk r m)) = mulM (invM (blk r m)) (invM (s x)) := by
    apply Matrix.of.injective
    rw [of_invM, of_mulM, of_mulM, of_invM, of_invM, Matrix.mul_inv_rev]
  rw [hw, one_mul, hi]
end GlobalTheory.GLFirstColumn
