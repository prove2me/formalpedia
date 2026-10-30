-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_omits_595
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T00:01:31.879702+00:00
-- url     : https://prove2.me/submissions/8323b599-72f0-454e-9456-0e8e7a795e20

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

theorem cache_omits_595_oai : ∀ p ∈ cache_595.H, ¬(p.1 = -2 ∧ p.2 ≤ -2) := by
  decide +kernel

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_omits_595_oai := @OAI.SnakyCertificate.Check.cache_omits_595_oai
