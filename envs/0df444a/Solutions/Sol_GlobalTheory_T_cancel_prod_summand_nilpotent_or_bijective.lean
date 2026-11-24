-- Prove2me | solution 1 for GlobalTheory.T.cancel_prod_summand_nilpotent_or_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:43.259713+00:00
-- url     : https://prove2.me/submissions/e251ba35-17d6-4fcc-bc23-2a437f6eec40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelProdSummandNilpotentOrBijective
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelProdSummandNilpotentOrBijectiveStatement
import Theorems.Thm_GlobalTheory_cancel_summand_nilpotent_or_bijective


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
theorem _root_.solution : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P], (∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f) → Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  first | exact @GlobalTheory.cancel_summand_nilpotent_or_bijective | exact GlobalTheory.cancel_summand_nilpotent_or_bijective | (intros; apply GlobalTheory.cancel_summand_nilpotent_or_bijective <;> assumption)
end _root_.GlobalTheory.T
