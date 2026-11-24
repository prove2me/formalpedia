-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.IwahoriUDL.di_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:56.406297+00:00
-- url     : https://prove2.me/submissions/39d878d6-2916-4830-b79c-094d44b9aeff

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsUdlOfIsUnit
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
theorem _root_.solution {I : Ideal R} {n : ℕ} {d : Matrix (Fin n) (Fin n) R} (hd : IsDi I d)
    {a : Matrix (Fin 1) (Fin 1) R} (ha : ∀ k k', a k k' - (1 : Matrix (Fin 1) (Fin 1) R) k k' ∈ I) :
    IsDi I ((fromBlocks d 0 0 a).submatrix (ex n).symm (ex n).symm) := by
  refine ⟨?_, ?_⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [one_ex, submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · simpa using hd.1 i j
    · simp
    · simp
    · simpa using ha i j
  · intro i j hij
    obtain ⟨i, rfl⟩ := (ex n).surjective i
    obtain ⟨j, rfl⟩ := (ex n).surjective j
    rw [submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    rcases i with i | i <;> rcases j with j | j
    · have : i ≠ j := fun h => hij (by rw [h])
      simpa using hd.2 i j this
    · simp
    · simp
    · exact absurd (by rw [Subsingleton.elim i j]) hij
end GlobalTheory.CompanionTheory.IwahoriUDL
