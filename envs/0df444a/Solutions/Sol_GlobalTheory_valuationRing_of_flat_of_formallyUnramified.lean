-- Prove2me | solution 1 for GlobalTheory.valuationRing_of_flat_of_formallyUnramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:42:17.984008+00:00
-- url     : https://prove2.me/submissions/02d68451-08c3-4f72-962a-7c046df5802b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ValuationRingOfFlatOfFormallyUnramified
import Theorems.Thm_GlobalTheory_isBezout_of_flat_of_formallyUnramified
import Theorems.Thm_GlobalTheory_isAlgebraic_of_flat_of_formallyUnramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (W B : Type) [CommRing W] [IsDomain W] [ValuationRing W] [CommRing B] [IsDomain B]
      [IsLocalRing B] [Algebra W B] [Module.Flat W B] [Algebra.EssFiniteType W B]
      [Algebra.FormallyUnramified W B], ValuationRing B ∧ Algebra.IsAlgebraic W B := by
  intro W B _ _ _ _ _ _ _ _ _ _
  have := isBezout_of_flat_of_formallyUnramified W B
  exact ⟨inferInstance, isAlgebraic_of_flat_of_formallyUnramified W B⟩
end GlobalTheory
