-- Prove2me | solution 2 for GlobalTheory.isLeftCoaction_comul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:27.818398+00:00
-- url     : https://prove2.me/submissions/26f614a5-e958-4fab-861f-777c2484a46a

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
variable (R C)
namespace GlobalTheory
theorem _root_.solution : IsLeftCoaction (comul : C →ₗ[R] C ⊗[R] C) where
  coassoc m := coassoc_apply m
  counit m := rTensor_counit_comul m
end GlobalTheory
