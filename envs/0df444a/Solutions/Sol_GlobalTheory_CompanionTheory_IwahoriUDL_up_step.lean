-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.up_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:41:02.505084+00:00
-- url     : https://prove2.me/submissions/55be8dd4-f1ab-4a32-970c-e28cdb50c54b

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
theorem _root_.solution {I : Ideal R} {n : ℕ} {u : Matrix (Fin n) (Fin n) R} (hu : IsUp I u)
    {x : Matrix (Fin n) (Fin 1) R} (hx : ∀ i k, x i k ∈ I) :
    IsUp I ((fromBlocks u x 0 1).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hu.1 i j
    · simpa using hx i j
    · simp
    · simp
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simp only [ex_inl, Fin.castSucc_lt_castSucc_iff] at hij
      simpa using hu.2.1 i j hij
    · simp only [ex_inl, ex_inr] at hij
      exact absurd hij (not_lt.mpr (Fin.le_last _))
    · simp
    · simp only [ex_inr, lt_self_iff_false] at hij
  · intro i
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    rw [submatrix_apply, Equiv.symm_apply_apply]
    rcases i with i | i
    · simpa using hu.2.2 i
    · simp
end GlobalTheory.CompanionTheory.IwahoriUDL
