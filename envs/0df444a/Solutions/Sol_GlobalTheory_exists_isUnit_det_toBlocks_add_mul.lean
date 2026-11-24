-- Prove2me | solution 1 for GlobalTheory.exists_isUnit_det_toBlocks_add_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:48:54.1933+00:00
-- url     : https://prove2.me/submissions/af673668-0605-418f-a3df-9541d5aef62f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualPairIsUnitDetBlocks
import Theorems.Thm_GlobalTheory_exists_det_add_mul_ne_zero_of_ker_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ}
    (H : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) (hH : IsUnit H.det) :
    ∃ X : Matrix (Fin n) (Fin n) R, IsUnit (H.toBlocks₁₁ + X * H.toBlocks₂₁).det := by
  classical
  set Hb := H.map (IsLocalRing.residue R) with hHb_def
  have hHb : Hb.det ≠ 0 := by
    rw [hHb_def, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hH.map (IsLocalRing.residue R)).ne_zero
  obtain ⟨Xb, hXb⟩ := exists_det_add_mul_ne_zero_of_ker_inf Hb.toBlocks₁₁ Hb.toBlocks₂₁ (by
    intro v h1 h2
    by_contra hv
    apply hHb
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨Sum.elim v 0, ?_, ?_⟩
    · intro h0
      apply hv
      funext i
      simpa using congrFun h0 (Sum.inl i)
    · funext i
      cases i with
      | inl i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁] using congrFun h1 i
      | inr i =>
        simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁] using congrFun h2 i)
  choose X hX using fun i j => IsLocalRing.residue_surjective (R := R) (Xb i j)
  refine ⟨Matrix.of X, ?_⟩
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
  have hm : (IsLocalRing.residue R).mapMatrix (H.toBlocks₁₁ + Matrix.of X * H.toBlocks₂₁) =
      Hb.toBlocks₁₁ + Xb * Hb.toBlocks₂₁ := by
    ext i j
    simp [RingHom.mapMatrix_apply, Matrix.mul_apply, map_sum, hX, hHb_def, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁]
  rw [hm]
  exact hXb
end GlobalTheory
