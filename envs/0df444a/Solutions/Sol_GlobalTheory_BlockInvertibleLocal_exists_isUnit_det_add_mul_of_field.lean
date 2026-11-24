-- Prove2me | solution 1 for GlobalTheory.BlockInvertibleLocal.exists_isUnit_det_add_mul_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:17:27.117826+00:00
-- url     : https://prove2.me/submissions/fca04f25-2eef-46d1-bb6a-f38b1a6dba5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsUnitDetAddMulOfFromBlocksLocalRing
import Theorems.Thm_GlobalTheory_BlockInvertibleLocal_exists_linearMap_injective_add_comp

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
theorem _root_.solution {k : Type} [Field k] {n : ℕ}
    (A B C D : Matrix (Fin n) (Fin n) k) (h : IsUnit (fromBlocks A B C D).det) :
    ∃ X : Matrix (Fin n) (Fin n) k, IsUnit (A + X * C).det := by
  have hinj : Function.Injective (fromBlocks A B C D).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 h)
  have hker : LinearMap.ker (toLin' A) ⊓ LinearMap.ker (toLin' C) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker, toLin'_apply, toLin'_apply] at hv
    have hz : (fromBlocks A B C D) *ᵥ (Sum.elim v 0) = (fromBlocks A B C D) *ᵥ 0 := by
      rw [fromBlocks_mulVec, mulVec_zero]
      ext i <;> cases i <;> simp [hv.1, hv.2]
    have h2 := hinj hz
    rw [Submodule.mem_bot]
    funext i
    exact congrFun h2 (Sum.inl i)
  obtain ⟨x, hx⟩ := exists_linearMap_injective_add_comp _ _ hker
  refine ⟨LinearMap.toMatrix' x, ?_⟩
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  convert hx using 1
  funext v
  simp [Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
end GlobalTheory.BlockInvertibleLocal
