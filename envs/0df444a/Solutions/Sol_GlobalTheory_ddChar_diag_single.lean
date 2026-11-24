-- Prove2me | solution 1 for GlobalTheory.ddChar_diag_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:52.442498+00:00
-- url     : https://prove2.me/submissions/c1d3b5af-347d-435f-8f20-c0bc9e271c50

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
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
theorem _root_.solution (ψ : GL n R →* A) (i j : n) (u : Rˣ) :
    ψ (ddCharDiag (Pi.mulSingle i u)) = ψ (ddCharDiag (Pi.mulSingle j u)) := by
  let σ := Equiv.swap i j
  let P : Matrix n n R := σ.toPEquiv.toMatrix
  have hPP : P * P = 1 := by
    ext a b
    rw [PEquiv.toMatrix_toPEquiv_mul]
    simp [P, σ, PEquiv.toMatrix_apply, Matrix.one_apply]
  let Pg : GL n R := ⟨P, P, hPP, hPP⟩
  have hconj : Pg * ddCharDiag (Pi.mulSingle i u) * Pg = ddCharDiag (Pi.mulSingle j u) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ddCharDiag_val, ddCharDiag_val]
    show P * _ * P = _
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp only [Matrix.submatrix_apply, id, diagonal_apply, σ, Equiv.symm_swap]
    by_cases hab : a = b
    · subst hab
      simp only [if_true]
      simp [Pi.mulSingle_apply, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    · have : Equiv.swap i j a ≠ Equiv.swap i j b := fun h => hab ((Equiv.swap i j).injective h)
      simp [hab, this]
  have h := congrArg ψ hconj
  rw [map_mul, map_mul, mul_comm (ψ Pg), mul_assoc, ← map_mul,
    show Pg * Pg = 1 from Units.ext hPP, map_one, mul_one] at h
  exact h
end GlobalTheory
