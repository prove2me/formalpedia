-- Prove2me | solution 1 for GlobalTheory.IsCoaction.comm_iff_mapsTo_torusWeightSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:40.937499+00:00
-- url     : https://prove2.me/submissions/e7fe81dd-a97f-49cd-b080-88d1ed2b9cc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Theorems.Thm_GlobalTheory_map_mem_coactionWeightSpace
import Theorems.Thm_GlobalTheory_mem_coactionWeightSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.mem_coactionWeightSpace



set_option autoImplicit false
open TensorProduct Coalgebra AddMonoidAlgebra DirectSum
open GlobalTheory
variable {R : Type*} [CommSemiring R] {X : Type*}
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']
variable [DecidableEq X]
omit [DecidableEq X]
namespace GlobalTheory
namespace IsCoaction
theorem _root_.solution {ρ : M →ₗ[R] M ⊗[R] R[X]} (h : IsCoaction ρ)
    (ρ' : M' →ₗ[R] M' ⊗[R] R[X]) (f : M →ₗ[R] M') :
    (∀ m, ρ' (f m) = f.rTensor R[X] (ρ m)) ↔
      ∀ x, ∀ m ∈ torusWeightSpace ρ x, f m ∈ torusWeightSpace ρ' x := by
  classical
  refine ⟨fun hf x m hm => map_mem_coactionWeightSpace hf hm, fun hf m => ?_⟩
  letI := h.decomposition
  induction m using Decomposition.inductionOn (torusWeightSpace ρ) with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | homogeneous m =>
    rw [mem_coactionWeightSpace.1 (hf _ _ m.2), mem_coactionWeightSpace.1 m.2,
      LinearMap.rTensor_tmul]
end IsCoaction
end GlobalTheory
