-- Prove2me | solution 2 for GlobalTheory.isCoaction_of_isGroupLikeElem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:38:42.778075+00:00
-- url     : https://prove2.me/submissions/78f4a5ff-625c-43f4-b663-179d5ca2e548

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
variable (M)
namespace GlobalTheory
theorem _root_.solution {g : C} (hg : IsGroupLikeElem R g) :
    IsCoaction ((TensorProduct.mk R M C).flip g) where
  coassoc m := by simp [hg.comul_eq_tmul_self]
  counit m := by simp [hg.counit_eq_one]
end GlobalTheory
