-- Prove2me | solution 1 for GlobalTheory.mem_coactionWeightSpace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:25.787714+00:00
-- url     : https://prove2.me/submissions/1e13cc7b-454f-41a9-9011-75cb52f0e639

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra
open GlobalTheory
variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']
omit [Coalgebra R C]
namespace GlobalTheory
theorem _root_.solution {ρ : M →ₗ[R] M ⊗[R] C} {g : C} {m : M} :
    m ∈ coactionWeightSpace ρ g ↔ ρ m = m ⊗ₜ[R] g := Iff.rfl
end GlobalTheory
