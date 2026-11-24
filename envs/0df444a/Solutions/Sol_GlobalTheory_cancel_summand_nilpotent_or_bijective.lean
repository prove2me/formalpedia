-- Prove2me | solution 1 for GlobalTheory.cancel_summand_nilpotent_or_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:32:45.659696+00:00
-- url     : https://prove2.me/submissions/1e287358-a0c3-4578-bbf8-40b444b478ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CancelProdSummandNilpotentOrBijective
import Theorems.Thm_GlobalTheory_linearEquiv_cancel_of_nilpotent_or_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (R M M' P : Type) [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup P] [Module R P],
    (∀ f : Module.End R P, IsNilpotent f ∨ Function.Bijective f) →
    Nonempty ((M × P) ≃ₗ[R] (M' × P)) → Nonempty (M ≃ₗ[R] M') := by
  intro R M M' P _ _ _ _ _ _ _ hP he
  obtain ⟨e⟩ := he
  exact linearEquiv_cancel_of_nilpotent_or_bijective hP e
end GlobalTheory
