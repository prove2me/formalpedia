-- Prove2me | solution 1 for GlobalTheory.T.divided_powers_valuations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:54.002801+00:00
-- url     : https://prove2.me/submissions/e430e7ad-067e-4ec3-8ded-abe0f66220a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DividedPowersValuations
import Definitions.Def_Formalism_PairingDivisors_StatementN
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DividedPowersValuationsStatement
import Theorems.Thm_GlobalTheory_legendre_divided_powers


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
theorem _root_.solution : Formalism.PairingDivisionLocalBalance.DivPow := by
  first | exact @GlobalTheory.legendre_divided_powers | exact GlobalTheory.legendre_divided_powers | (intros; apply GlobalTheory.legendre_divided_powers <;> assumption)
end _root_.GlobalTheory.T
