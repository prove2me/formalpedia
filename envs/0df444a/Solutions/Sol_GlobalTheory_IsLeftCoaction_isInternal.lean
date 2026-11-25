-- Prove2me | solution 1 for GlobalTheory.IsLeftCoaction.isInternal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:56:55.57474+00:00
-- url     : https://prove2.me/submissions/92dd698b-7f9f-409d-91ac-22966d180da9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TensorCoeffOfMemTorusWeightSpace
import Theorems.Thm_GlobalTheory_isLeftCoaction_iff_isCoaction_comm
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
namespace GlobalTheory
namespace IsLeftCoaction
theorem _root_.solution {ρ : M →ₗ[R] R[X] ⊗[R] M} (h : IsLeftCoaction ρ) :
    IsInternal fun x : X => LinearMap.eqLocus ρ (TensorProduct.mk R R[X] M (single x 1)) := by
  have := ((isLeftCoaction_iff_isCoaction_comm ρ).1 h).isInternal_torusWeightSpace
  convert this using 2 with x
  ext m
  rw [mem_coactionWeightSpace, ← (TensorProduct.comm R M R[X]).apply_eq_iff_eq]
  simp
end IsLeftCoaction
end GlobalTheory
