-- Prove2me | solution 1 for GlobalTheory.T.inertiaDeg_bot_eq_finrank_finite_domain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:23:24.790286+00:00
-- url     : https://prove2.me/submissions/296c4ea4-eeda-4f7e-8476-6f7867f816d5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertiaDegBotEqFinrankFiniteDomain
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertiaDegBotEqFinrankFiniteDomainStatement
import Theorems.Thm_GlobalTheory_inertiaDeg_bot_eq_finrank


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R S : Type) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S], Function.Injective (algebraMap R S) → (⊥ : Ideal S).inertiaDeg R = Module.finrank R S := by
  first | exact @GlobalTheory.inertiaDeg_bot_eq_finrank | exact GlobalTheory.inertiaDeg_bot_eq_finrank | (intros; apply GlobalTheory.inertiaDeg_bot_eq_finrank <;> assumption)
end _root_.GlobalTheory.T
