-- Prove2me | solution 1 for GlobalTheory.map_mem_coactionWeightSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:19:57.422671+00:00
-- url     : https://prove2.me/submissions/1fa61c17-622e-4bc6-b9e0-4cfe064dca12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
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
open TensorProduct Coalgebra
open GlobalTheory
variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']
omit [Coalgebra R C]
namespace GlobalTheory
theorem _root_.solution {ρ : M →ₗ[R] M ⊗[R] C} {ρ' : M' →ₗ[R] M' ⊗[R] C}
    {f : M →ₗ[R] M'} (hf : ∀ m, ρ' (f m) = f.rTensor C (ρ m)) {g : C} {m : M}
    (hm : m ∈ coactionWeightSpace ρ g) : f m ∈ coactionWeightSpace ρ' g := by
  rw [mem_coactionWeightSpace] at hm ⊢
  rw [hf, hm, LinearMap.rTensor_tmul]
end GlobalTheory
