-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Matrixlemmas.exists_GL_vecMul_eq_single_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:52:45.913614+00:00
-- url     : https://prove2.me/submissions/d1494674-dc54-4ad0-b012-0598df1c4b66

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsGLVecMulEqLastBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Matrixlemmas
namespace GlobalTheory.CompanionTheory.Matrixlemmas
theorem _root_.solution {k : Type} [Field k] (n : ℕ) (ξ : Fin (n + 1) → k) (hξ : ξ ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k,
      Matrix.vecMul ξ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = Pi.single (Fin.last n) 1 := by
  classical
  obtain ⟨c, hc⟩ : ∃ c, ξ c ≠ 0 := by
    by_contra hcon
    exact hξ (funext fun i => by_contra fun hi => hcon ⟨i, hi⟩)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap c (Fin.last n)
  let U : Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateRow c ξ
  have hU : U.det = ξ c := by
    have hT : Uᵀ = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol c ξ := by
      simp only [U]
      rw [← Matrix.updateCol_transpose, Matrix.transpose_one]
    rw [← Matrix.det_transpose, hT, ← Matrix.cramer_apply, Matrix.cramer_one]
    rfl
  let h : Matrix (Fin (n + 1)) (Fin (n + 1)) k := U.submatrix σ id
  have hdet : IsUnit h.det := by
    have : h.det = Equiv.Perm.sign σ * U.det := Matrix.det_permute σ U
    rw [this, hU]
    refine IsUnit.mul ?_ (isUnit_iff_ne_zero.mpr hc)
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]
  have hrow : Matrix.vecMul (Pi.single (Fin.last n) 1) h = ξ := by
    rw [Matrix.single_one_vecMul]
    funext j
    simp [h, U, σ]
  refine ⟨(Matrix.nonsingInvUnit h hdet)⁻¹, ?_⟩
  have hinv : h * (((Matrix.nonsingInvUnit h hdet)⁻¹ : GL (Fin (n + 1)) k) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) k) = 1 :=
    (Matrix.nonsingInvUnit h hdet).mul_inv
  conv_lhs => rw [← hrow]
  rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
end GlobalTheory.CompanionTheory.Matrixlemmas
