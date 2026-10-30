-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_omits_603
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T00:01:54.079875+00:00
-- url     : https://prove2.me/submissions/4a1857d5-d1fe-44d2-86f1-402ecc60478a

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

theorem cache_omits_603_oai : ∀ p ∈ cache_603.H, ¬(p.1 ≤ -3 ∧ p.2 = 0) := by
  decide +kernel

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_omits_603_oai := @OAI.SnakyCertificate.Check.cache_omits_603_oai
