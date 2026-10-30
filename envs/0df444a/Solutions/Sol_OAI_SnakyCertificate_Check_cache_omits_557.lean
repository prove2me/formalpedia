-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_omits_557
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T00:01:09.005397+00:00
-- url     : https://prove2.me/submissions/e06c609b-a97d-4a5f-ba88-5507a485ae74

import Mathlib
import Definitions.Def_SnakyCertificate
import Definitions.Def_OAIQ114S000

section
-- module Solutions.OAIQ114_SC.SnakyCertificate_Summaries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SnakyCertificate.Check

theorem cache_omits_557_oai : ∀ p ∈ cache_557.H, ¬(p.1 ≤ -3 ∧ p.2 ≤ -2) := by
  decide +kernel

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_omits_557_oai := @OAI.SnakyCertificate.Check.cache_omits_557_oai
