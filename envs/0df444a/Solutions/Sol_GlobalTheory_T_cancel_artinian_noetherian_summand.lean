-- Prove2me | solution 1 for GlobalTheory.T.cancel_artinian_noetherian_summand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:00:19.415144+00:00
-- url     : https://prove2.me/submissions/4cfbab72-55d2-485e-a1d3-341b0a767bf9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummand
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelArtinianNoetherianSummandStatement
import Theorems.Thm_GlobalTheory_ks_cancel


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
theorem _root_.solution : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P] [IsArtinian R P] [IsNoetherian R P], Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  first | exact @GlobalTheory.ks_cancel | exact GlobalTheory.ks_cancel | (intros; apply GlobalTheory.ks_cancel <;> assumption)
end _root_.GlobalTheory.T
