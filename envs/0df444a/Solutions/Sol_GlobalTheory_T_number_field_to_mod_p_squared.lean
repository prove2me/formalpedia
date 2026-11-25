-- Prove2me | solution 1 for GlobalTheory.T.number_field_to_mod_p_squared
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:52:39.646796+00:00
-- url     : https://prove2.me/submissions/28d4b772-529b-49e0-9bf8-d0a95a2baa43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NumberFieldToModPSquared
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_NumberFieldToModPSquared
import Theorems.Thm_GlobalTheory_exists_prime_sq_ringHom_of_closure


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Polynomial
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (S : Finset K) (n : ℕ), ∃ p : ℕ, p.Prime ∧ n < p ∧ Nonempty (Subring.closure (S : Set K) →+* ZMod (p ^ 2)) := by
  first | exact @_root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | exact _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure | (intros; apply _root_.GlobalTheory.exists_prime_sq_ringHom_of_closure <;> assumption)
end _root_.GlobalTheory.T
