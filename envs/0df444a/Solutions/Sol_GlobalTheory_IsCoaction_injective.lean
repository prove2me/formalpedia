-- Prove2me | solution 1 for GlobalTheory.IsCoaction.injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:55:52.915203+00:00
-- url     : https://prove2.me/submissions/2ea253aa-e45e-4b9f-8140-e16bfefed96b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
import Theorems.Thm_GlobalTheory_IsCoaction_rid_counit

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
namespace GlobalTheory
namespace IsCoaction
theorem _root_.solution {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) : Function.Injective ρ :=
  Function.LeftInverse.injective
    (g := fun t => TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M t))
    h.rid_counit
end IsCoaction
end GlobalTheory
