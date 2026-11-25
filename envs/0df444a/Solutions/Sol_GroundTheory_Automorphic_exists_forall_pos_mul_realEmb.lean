-- Prove2me | solution 1 for GroundTheory.Automorphic.exists_forall_pos_mul_realEmb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:12:46.286002+00:00
-- url     : https://prove2.me/submissions/03efd8c7-dc2a-46a0-82be-51e6e7dcfea6

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_Places
import Theorems.Thm_GroundTheory_Automorphic_realEmb_eq_extension
import Theorems.Thm_GroundTheory_Automorphic_conj_conj
import Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
import Theorems.Thm_GroundTheory_Automorphic_matrixCoords_zero
import Theorems.Thm_GroundTheory_Automorphic_unitaryPiEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.conj_conj
attribute [local simp] GroundTheory.Automorphic.hermTraceBilin_apply
attribute [local simp] GroundTheory.Automorphic.matrixCoords_zero
attribute [local simp] GroundTheory.Automorphic.unitaryPiEquiv_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct NumberField NumberField.InfinitePlace
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Automorphic
theorem _root_.solution (hreal : ∀ w : InfinitePlace K, w.IsReal)
    (ε : InfinitePlace K → ℝ) (hε : ∀ w, ε w ≠ 0) :
    ∃ θ : K, ∀ w, 0 < ε w * realEmb hreal w θ := by
  let ψ := fun w : InfinitePlace K => Completion.ringEquivRealOfIsReal (hreal w)
  have hψc : ∀ w, Continuous (Completion.extensionEmbeddingOfIsReal (hreal w)) := fun w =>
    (Completion.isometry_extensionEmbeddingOfIsReal (hreal w)).continuous
  let U : Set (InfiniteAdeleRing K) :=
    ⋂ w, {q | 0 < ε w * Completion.extensionEmbeddingOfIsReal (hreal w) (q w)}
  have hU : IsOpen U := isOpen_iInter_of_finite fun w =>
    isOpen_lt continuous_const (continuous_const.mul ((hψc w).comp (continuous_apply w)))
  let p : InfiniteAdeleRing K := fun w => (ψ w).symm (ε w)
  have hp : p ∈ U := by
    simp only [U, Set.mem_iInter, Set.mem_ofPred_eq]
    intro w
    have : Completion.extensionEmbeddingOfIsReal (hreal w) (p w) = ε w :=
      (ψ w).apply_symm_apply (ε w)
    rw [this]
    exact mul_self_pos.2 (hε w)
  obtain ⟨θ, hθ⟩ := (InfiniteAdeleRing.denseRange_algebraMap (K := K)).exists_mem_open hU ⟨p, hp⟩
  refine ⟨θ, fun w => ?_⟩
  have := Set.mem_iInter.1 hθ w
  simp only [Set.mem_ofPred_eq] at this
  rwa [show (algebraMap K (InfiniteAdeleRing K) θ) w = algebraMap K w.Completion θ from rfl,
    realEmb_eq_extension] at this
end GroundTheory.Automorphic
