-- Prove2me | solution 1 for GlobalTheory.LeadingMinorInv.minor_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:34:42.298811+00:00
-- url     : https://prove2.me/submissions/baece2ea-f5fc-4479-bb3a-df043b9a7238

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.LeadingMinorInv
open Formalism.QuantumDeterminants
namespace GlobalTheory.LeadingMinorInv
theorem _root_.solution {n l : ℕ} (hl : l ≤ n) (A U : Matrix (Fin n) (Fin n) ℂ) (hU : UpUni U) :
    ((A * U).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      (A.submatrix (Fin.castLE hl) (Fin.castLE hl)).det := by
  have hsub : (A * U).submatrix (Fin.castLE hl) (Fin.castLE hl) =
      A.submatrix (Fin.castLE hl) (Fin.castLE hl) * U.submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    apply Fintype.sum_of_injective (Fin.castLE hl) (Fin.castLE_injective hl)
    · intro b hb
      have hjb : Fin.castLE hl j < b := by
        rw [Fin.lt_def]
        show j.val < b.val
        by_contra hc
        have := j.isLt
        exact hb ⟨⟨b.val, by omega⟩, Fin.ext rfl⟩
      rw [hU.1 b _ hjb, mul_zero]
    · intro a
      rfl
  have hdet : (U.submatrix (Fin.castLE hl) (Fin.castLE hl)).det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [Matrix.submatrix_apply, hU.2]
    · intro i j hij
      simp only [Matrix.submatrix_apply]
      apply hU.1
      rw [Fin.lt_def] at hij ⊢
      exact hij
  rw [hsub, Matrix.det_mul, hdet, mul_one]
end GlobalTheory.LeadingMinorInv
