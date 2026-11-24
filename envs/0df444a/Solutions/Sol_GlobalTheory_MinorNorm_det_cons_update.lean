-- Prove2me | solution 1 for GlobalTheory.MinorNorm.det_cons_update
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:30:30.561176+00:00
-- url     : https://prove2.me/submissions/bcccf020-8a39-4f98-b53b-16335627a054

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
variable {R : Type} [CommRing R] [Algebra ℂ R]
namespace GlobalTheory.MinorNorm
theorem _root_.solution {m : ℕ} (M : Fin m → Fin (m + 1) → R) (t : Fin m) (e : Fin (m + 1) → R) :
    (Matrix.of (Fin.cons (M t) (Function.update M t e) : Fin (m + 1) → Fin (m + 1) → R)).det =
      -(Matrix.of (Fin.cons e M : Fin (m + 1) → Fin (m + 1) → R)).det := by
  have h := det_permute (Equiv.swap (0 : Fin (m + 1)) t.succ)
    (Matrix.of (Fin.cons e M : Fin (m + 1) → Fin (m + 1) → R))
  rw [Equiv.Perm.sign_swap (Fin.succ_ne_zero t).symm] at h
  simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_mul, one_mul] at h
  rw [← h]
  congr 1
  ext i u
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [-Fin.cons_update]
  · by_cases hi : i = t
    · subst hi; simp
    · rw [submatrix_apply, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i)
        (fun h => hi (Fin.succ_injective _ h))]
      simp [-Fin.cons_update, Function.update_of_ne hi]
end GlobalTheory.MinorNorm
