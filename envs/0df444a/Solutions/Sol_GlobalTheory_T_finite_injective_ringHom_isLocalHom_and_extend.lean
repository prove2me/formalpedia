-- Prove2me | solution 1 for GlobalTheory.T.finite_injective_ringHom_isLocalHom_and_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:17:13.595358+00:00
-- url     : https://prove2.me/submissions/cfa29947-760e-4aa2-aea9-f2b04fe0f5a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteInjectiveRingHomIsLocalHomAndExtend
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FiniteInjectiveRingHomIsLocalHomAndExtendStatement
import Theorems.Thm_GlobalTheory_finite_injective_localHom_and_extend


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V R K : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [IsAlgClosed K] (ρ : V →+* R), Function.Injective ρ → ρ.Finite → IsLocalHom ρ ∧ ∀ ev : V →+* K, ∃ ev₁ : R →+* K, ev₁.comp ρ = ev := by
  first | exact @GlobalTheory.finite_injective_localHom_and_extend | exact GlobalTheory.finite_injective_localHom_and_extend | (intros; apply GlobalTheory.finite_injective_localHom_and_extend <;> assumption)
end _root_.GlobalTheory.T
