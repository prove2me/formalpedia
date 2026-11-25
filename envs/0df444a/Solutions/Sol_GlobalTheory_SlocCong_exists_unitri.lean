-- Prove2me | solution 1 for GlobalTheory.SlocCong.exists_unitri
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:47:44.246077+00:00
-- url     : https://prove2.me/submissions/2baafa8f-24a2-4c57-b20c-bfbf0de12c08

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermFamiliesCongrModUnitriangular
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open Formalism.MainNotions.S
open GlobalTheory GlobalTheory.SlocCong
namespace GlobalTheory.SlocCong
theorem _root_.solution {R : Type} [CommRing R] {n : ℕ} (W W' : Matrix (Fin n) (Fin n) R)
    (hW : ∀ a b, b < a → W a b = 0) (hW' : ∀ a b, b < a → W' a b = 0) (hd : ∀ a, W' a a = W a a)
    (hu : ∀ a, IsUnit (W a a)) :
    ∃ ξ : Matrix (Fin n) (Fin n) R, (∀ a b, b < a → ξ a b = 0) ∧ (∀ a, ξ a a = 1) ∧ W * ξ = W' := by
  have hbt : W.BlockTriangular id := fun i j h => hW i j h
  have hbt' : W'.BlockTriangular id := fun i j h => hW' i j h
  have hdet : IsUnit W.det := by
    rw [Matrix.det_of_upperTriangular hbt]
    exact IsUnit.prod_univ_iff.2 hu
  haveI := W.invertibleOfIsUnitDet hdet
  have hinv : W⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have diag : ∀ P Q : Matrix (Fin n) (Fin n) R, P.BlockTriangular id → Q.BlockTriangular id →
      ∀ a, (P * Q) a a = P a a * Q a a := by
    intro P Q hP hQ a
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_single a (fun c _ hc => ?_) (by simp)
    rcases lt_or_gt_of_ne hc with h | h
    · rw [hP h, zero_mul]
    · rw [hQ h, mul_zero]
  refine ⟨W⁻¹ * W', fun a b h => (hinv.mul hbt') h, fun a => ?_, ?_⟩
  · rw [diag _ _ hinv hbt', hd, ← diag _ _ hinv hbt, Matrix.nonsing_inv_mul _ hdet, Matrix.one_apply_eq]
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
end GlobalTheory.SlocCong
