-- Prove2me | solution 1 for GlobalTheory.exists_orthonormal_frameMul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:13.905797+00:00
-- url     : https://prove2.me/submissions/46920c45-8b48-484b-9615-fa84d552fbf4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} [Fintype ι] {r : ι → ℕ} {𝕜 : Type*} [RCLike 𝕜] {V : ι → Type*}
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [∀ s, NormedAddCommGroup (V s)] [∀ s, InnerProductSpace 𝕜 (V s)]
  [∀ s, FiniteDimensional 𝕜 (V s)]
namespace GlobalTheory
theorem _root_.solution (hV : ∀ s, finrank 𝕜 (V s) = r s)
    (x : ∀ s, Fin (r s) → V s) :
    ∃ (y : ∀ s, Fin (r s) → V s) (b : ∀ s, Matrix (Fin (r s)) (Fin (r s)) 𝕜),
      (∀ s, Orthonormal 𝕜 (y s)) ∧ (∀ s, (b s).IsUpperTriangular) ∧
        (∀ s i, ‖b s i i‖ ≤ ‖x s i‖) ∧ frameMul y b = x := by
  have h : ∀ s, finrank 𝕜 (V s) = Fintype.card (Fin (r s)) := fun s => by simp [hV]
  let e := fun s => InnerProductSpace.gramSchmidtOrthonormalBasis (h s) (x s)
  refine ⟨fun s => e s, fun s => (e s).toBasis.toMatrix (x s), fun s => (e s).orthonormal,
    fun s => InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular (h s) (x s),
    fun s i => ?_, ?_⟩
  · change ‖(e s).toBasis.toMatrix (x s) i i‖ ≤ _
    rw [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    refine (norm_inner_le_norm _ _).trans ?_
    rw [(e s).orthonormal.1 i, one_mul]
  · funext s j
    exact (e s).toBasis.sum_toMatrix_smul_self (x s) j
end GlobalTheory
