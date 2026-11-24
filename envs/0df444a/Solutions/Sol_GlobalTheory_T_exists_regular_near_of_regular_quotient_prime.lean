-- Prove2me | solution 1 for GlobalTheory.T.exists_regular_near_of_regular_quotient_prime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:08:05.063734+00:00
-- url     : https://prove2.me/submissions/18dc8c22-c10f-46dc-bb04-0b6db411781c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrime
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrimeStatement
import Theorems.Thm_GlobalTheory_RegularAscent_exists_regular_near_of_regular_quotient


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (p : Ideal B) [p.IsPrime], IsRegularLocalRing (Localization.AtPrime p) → ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) → IsRegularLocalRing (Localization.AtPrime q) := by
  first | exact @GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | exact GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient | (intros; apply GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient <;> assumption)
end _root_.GlobalTheory.T
