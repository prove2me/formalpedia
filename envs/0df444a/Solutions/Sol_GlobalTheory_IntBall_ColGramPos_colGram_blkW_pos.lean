-- Prove2me | solution 1 for GlobalTheory.IntBall.ColGramPos.colGram_blkW_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:46:41.514462+00:00
-- url     : https://prove2.me/submissions/e22b68fc-546d-4639-95c7-5bef17242378

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ColumnGramDeterminantDiagonalBlockUnitLowerPos
import Theorems.Thm_GlobalTheory_IntBall_ColGramPos_blkW_upper
import Theorems.Thm_GlobalTheory_IntBall_ColGramPos_blkW_diag
import Theorems.Thm_GlobalTheory_IntBall_ColGramPos_lowerTri_det_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix
open GlobalTheory GlobalTheory.IntBall GlobalTheory.IntBall.ColGramPos
open scoped ComplexOrder
namespace GlobalTheory.IntBall.ColGramPos
theorem _root_.solution : ∀ (r p0 : ℕ) (w : Low r → ℂ) (k : Fin (r - 1 + 1)), 0 < colGram (blkW p0 w) k := by
  intro r p0 w k
  set B := blkW p0 w with hB
  have hk : (k : ℕ) ≤ r - 1 := Nat.le_of_lt_succ k.isLt
  set N : Matrix (Fin (r - 1)) (Fin k) ℂ := B.submatrix id (Fin.castLE hk) with hN
  have hsub : (Bᴴ * B).submatrix (Fin.castLE hk) (Fin.castLE hk) = Nᴴ * N := by
    ext a b
    simp [N, Matrix.mul_apply, Matrix.conjTranspose_apply]
  set T : Matrix (Fin k) (Fin k) ℂ := B.submatrix (Fin.castLE hk) (Fin.castLE hk) with hT
  have hTdet : T.det = 1 := by
    apply lowerTri_det_one
    · intro i j hij
      exact blkW_upper p0 w _ _ (by rw [Fin.lt_def] at hij ⊢; simpa using hij)
    · intro i
      exact blkW_diag p0 w _
  have hinj : Function.Injective N.mulVec := by
    intro u v huv
    have h0 : N *ᵥ (u - v) = 0 := by rw [Matrix.mulVec_sub, huv, sub_self]
    have hT0 : T *ᵥ (u - v) = 0 := by
      ext i
      have := congrFun h0 (Fin.castLE hk i)
      simpa [T, N, Matrix.mulVec, dotProduct] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero (by rw [hTdet]; exact one_ne_zero) hT0
    exact sub_eq_zero.mp this
  have hpd : (Nᴴ * N).PosDef := Matrix.PosDef.conjTranspose_mul_self N hinj
  have hdet : (Nᴴ * N).det ≠ 0 := hpd.det_pos.ne'
  unfold colGram lminor
  rw [hsub]
  exact norm_pos_iff.mpr hdet
end GlobalTheory.IntBall.ColGramPos
