-- Prove2me | solution 1 for GlobalTheory.dmin_rmul_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:50:41.670932+00:00
-- url     : https://prove2.me/submissions/726959c6-fb5b-41dc-a058-e571cc9f0a6d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
import Theorems.Thm_GlobalTheory_norm_gram_sign_sub_le
import Theorems.Thm_GlobalTheory_norm_prod_sign_mul_det_submatrix_sub_one_le
import Theorems.Thm_GlobalTheory_re_pos_and_abs_log_norm_le
import Theorems.Thm_GlobalTheory_gram_eq_transpose_mul_mul_map_star
import Theorems.Thm_GlobalTheory_gram_mul_eq_transpose_mul_gram_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (X : Data E r) (x : Frame X.Ψ r)
    (hx : ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) =
      Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))
    (A : Frame X.Ψ r) {δ : ℝ} (hδ : 0 ≤ δ) (hr : (r : ℝ) ^ 2 * δ ≤ 1 / 100)
    (hA : ∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ δ) :
    rmul x A ∈ X.dom ∧ ∀ τ i, dmin X.Gm (rmul x A) τ i ≠ 0 ∧
      |Real.log ‖dmin X.Gm (rmul x A) τ i‖| ≤ 9 * ((r : ℝ) ^ 2 * δ) := by
  set j : Fin r → ℂ := fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hjdef
  have hj : ∀ a, j a = 1 ∨ j a = -1 := fun a => by
    simp only [hjdef, sgn]
    split_ifs <;> simp
  have hj1 : ∀ a, ‖j a‖ = 1 := fun a => by rcases hj a with h | h <;> simp [h]
  have hrr : (r : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow two_ne_zero r
  have hG : ∀ (τ : X.Ψ) a b, ‖(gram τ.1 X.Gm (mat (rmul x A) τ) - diagonal j) a b‖ ≤ 3 * δ := by
    intro τ a b
    have h1 : mat (rmul x A) τ = mat x τ * (1 + (mat A τ - 1)) := by
      rw [add_sub_cancel]; rfl
    rw [h1, gram_mul_eq_transpose_mul_gram_mul, hx]
    refine norm_gram_sign_sub_le j hj1 _ hδ (by nlinarith) (fun a b => ?_) a b
    simpa [mat, one_apply] using hA τ a b
  have hmin : ∀ (τ : X.Ψ) {i : ℕ} {e : Fin i → Fin r}, Function.Injective e →
      0 < ((∏ a, j (e a)) * ((gram τ.1 X.Gm (mat (rmul x A) τ)).submatrix e e).det).re ∧
      |Real.log ‖(∏ a, j (e a)) * ((gram τ.1 X.Gm (mat (rmul x A) τ)).submatrix e e).det‖| ≤
        3 * ((r : ℝ) ^ 2 * (3 * δ)) := fun τ i e he =>
    re_pos_and_abs_log_norm_le (by linarith)
      (norm_prod_sign_mul_det_submatrix_sub_one_le j hj _ (by positivity) (hG τ) (by linarith) he)
  refine ⟨fun τ => ⟨fun h0 => ?_, fun i => ?_⟩, fun τ i => ?_⟩
  · have h := (hmin τ Function.injective_id).1
    rw [submatrix_id_id, gram_eq_transpose_mul_mul_map_star, det_mul, det_mul, det_transpose,
      h0] at h
    simp at h
  · have h := (hmin τ (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))).1
    have h1 : (∏ a, j (Fin.castLE (Nat.le_of_lt_succ i.isLt) a)) = ((psgn X.p0 i : ℝ) : ℂ) := by
      rw [psgn, Finset.prod_range, Complex.ofReal_prod]
      rfl
    rw [h1, Complex.re_ofReal_mul] at h
    exact h
  · obtain ⟨h1, h2⟩ := hmin τ (Fin.castLE_injective (Nat.le_of_lt_succ i.isLt))
    refine ⟨fun h0 => ?_, ?_⟩
    · rw [dmin, lminor] at h0
      rw [h0] at h1
      simp at h1
    · rw [norm_mul, norm_prod, Finset.prod_eq_one (fun a _ => hj1 _), one_mul] at h2
      rw [dmin, lminor]
      linarith
end GlobalTheory
