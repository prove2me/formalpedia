-- Prove2me | solution 1 for GlobalTheory.ddChar_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:54.622846+00:00
-- url     : https://prove2.me/submissions/e4d3b8ee-53d0-4a72-8654-7351651e49e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
import Theorems.Thm_GlobalTheory_ddChar_unip_eq_one
import Theorems.Thm_GlobalTheory_ddCharDiag_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
namespace GlobalTheory
theorem _root_.solution (ψ : GL n R →* A) (u : Rˣ) (hu : IsUnit ((u : R) - 1)) (a : n) (y : n → R)
    (hy : y a = 0) (h : y ⬝ᵥ Pi.single a 1 = 0) :
    ψ (ddCharUnip _ (ddChar_vecMulVec_sq h)) = 1 := by
  refine ddChar_unip_eq_one ψ _ _ (ddCharDiag (Pi.mulSingle a u)) (u : R) 1 ?_ ?_ ?_
  · ext i j
    rw [ddCharDiag_val, Matrix.diagonal_mul, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    by_cases hi : i = a
    · subst hi
      simp
    · simp [hi]
  · ext i j
    rw [ddCharDiag_val, Matrix.mul_diagonal, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul, one_mul]
    by_cases hj : j = a
    · subst hj
      simp [hy]
    · simp [hj]
  · rw [← neg_sub]
    exact hu.neg
end GlobalTheory
