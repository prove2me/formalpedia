-- Prove2me | solution 1 for GlobalTheory.IsCoaction.rid_counit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:53:50.359467+00:00
-- url     : https://prove2.me/submissions/169a89a4-699b-4626-93f4-25b8703eec4a

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
namespace GlobalTheory
namespace IsCoaction
theorem _root_.solution {ρ : M →ₗ[R] M ⊗[R] C} (h : IsCoaction ρ) (m : M) :
    TensorProduct.rid R M ((Coalgebra.counit : C →ₗ[R] R).lTensor M (ρ m)) = m := by
  simp [h.counit]
end IsCoaction
end GlobalTheory
