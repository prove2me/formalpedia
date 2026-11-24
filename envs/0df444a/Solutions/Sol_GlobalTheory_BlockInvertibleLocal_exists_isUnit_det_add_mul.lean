-- Prove2me | solution 1 for GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:32:59.18235+00:00
-- url     : https://prove2.me/submissions/99ed0f3e-f2a5-4c88-b5ed-1e3866e59970

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitDetAddMulOfFromBlocksLocalRing
import Theorems.Thm_GlobalTheory_BlockInvertibleLocal_exists_isUnit_det_add_mul_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.BlockInvertibleLocal
namespace GlobalTheory.BlockInvertibleLocal
theorem _root_.solution : ∀ {O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) O),
    IsUnit (Matrix.fromBlocks A B C D).det → ∃ X : Matrix (Fin n) (Fin n) O, IsUnit (A + X * C).det := by
  intro O _ _ n A B C D h
  have h' : IsUnit (fromBlocks (A.map (IsLocalRing.residue O)) (B.map (IsLocalRing.residue O))
      (C.map (IsLocalRing.residue O)) (D.map (IsLocalRing.residue O))).det := by
    rw [← fromBlocks_map]
    have := h.map (IsLocalRing.residue O)
    rwa [RingHom.map_det] at this
  obtain ⟨Y, hY⟩ := exists_isUnit_det_add_mul_of_field _ _ _ _ h'
  obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin n) O, X.map (IsLocalRing.residue O) = Y :=
    ⟨Y.map (Function.surjInv IsLocalRing.residue_surjective), by
      ext i j; simp [Function.surjInv_eq]⟩
  refine ⟨X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add _), Matrix.map_mul, hX]
  exact hY.ne_zero
end GlobalTheory.BlockInvertibleLocal
