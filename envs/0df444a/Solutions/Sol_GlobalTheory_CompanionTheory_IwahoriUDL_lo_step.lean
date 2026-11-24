-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.lo_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:58.469086+00:00
-- url     : https://prove2.me/submissions/9432d039-0104-40d5-8cf2-6ace3d47b759

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_ex_inl
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_ex_inr
import Theorems.Thm_GlobalTheory_CompanionTheory_IwahoriUDL_one_ex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IwahoriUDL
open Matrix
variable {R : Type*} [CommRing R]
namespace GlobalTheory.CompanionTheory.IwahoriUDL
theorem _root_.solution {I : Ideal R} {n : ℕ} {l : Matrix (Fin n) (Fin n) R} (hl : IsLo I l)
    {y : Matrix (Fin 1) (Fin n) R} (hy : ∀ k j, y k j ∈ I) :
    IsLo I ((fromBlocks l 0 y 1).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hl.1 i j
    · simp
    · simpa using hy i j
    · simp
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp only [ex_inl, Fin.castSucc_lt_castSucc_iff] at hij
      simpa using hl.2.1 i j hij
    · simp
    · simp only [ex_inl, ex_inr] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last _))
    · simp only [ex_inr, lt_self_iff_false] at hij
  · intro i
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · simpa using hl.2.2 i
    · simp
end GlobalTheory.CompanionTheory.IwahoriUDL
