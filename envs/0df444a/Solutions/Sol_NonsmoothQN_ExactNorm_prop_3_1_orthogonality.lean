-- Prove2me | solution 1 for NonsmoothQN.ExactNorm.prop_3_1_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:59:39.754339+00:00
-- url     : https://prove2.me/submissions/251e56d5-2fa8-4f60-8b64-2bc86a76b30e

import Mathlib
import Definitions.Def_NonsmoothQN_ExactNorm_Basic

set_option autoImplicit false
open Matrix Filter Topology NonsmoothQN.ExactNorm

theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ)
    (xk pk gk xk1 gk1 : Fin n → ℝ) (Hk Hk1 : Matrix (Fin n) (Fin n) ℝ) (tk : ℝ)
    (hHk : Hk.PosDef) (hHk1 : Hk1.PosDef)
    (hgk : IsGradAt f gk xk) (hpk : pk = -(Hk *ᵥ gk))
    (htk : 0 < tk) (hxk1 : xk1 = xk + tk • pk)
    (hmin : IsLocalMin (fun τ : ℝ => f (xk + τ • pk)) tk)
    (hgk1 : IsGradAt f gk1 xk1)
    (hsec : Hk1 *ᵥ (gk1 - gk) = tk • pk) :
    (-(Hk1 *ᵥ gk1)) ⬝ᵥ (gk1 - gk) = 0 := by
  -- derivative of the line function at tk vanishes
  have hline : HasDerivAt (fun τ : ℝ => f (xk + τ • pk)) (gk1 ⬝ᵥ pk) tk := by
    have hd : HasFDerivAt f (fderiv ℝ f xk1) xk1 := hgk1.1.hasFDerivAt
    have hinner : HasDerivAt (fun τ : ℝ => xk + τ • pk) pk tk := by
      simpa using ((hasDerivAt_id tk).smul_const pk).const_add xk
    have hd' : HasFDerivAt f (fderiv ℝ f xk1) (xk + tk • pk) := by rw [← hxk1]; exact hd
    have := hd'.comp_hasDerivAt tk hinner
    rw [hgk1.2] at this
    exact this
  have h0 : gk1 ⬝ᵥ pk = 0 := hmin.hasDerivAt_eq_zero hline
  have hsymm : Hk1ᵀ = Hk1 := by
    have := hHk1.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have key : ∀ w : Fin n → ℝ, (Hk1 *ᵥ gk1) ⬝ᵥ w = gk1 ⬝ᵥ (Hk1 *ᵥ w) := by
    intro w
    rw [dotProduct_comm (Hk1 *ᵥ gk1), dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm,
      dotProduct_comm]
  rw [neg_dotProduct, key, hsec, dotProduct_smul, h0]
  simp
