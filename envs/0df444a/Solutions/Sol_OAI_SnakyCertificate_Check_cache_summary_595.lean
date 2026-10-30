-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_summary_595
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T00:03:01.32197+00:00
-- url     : https://prove2.me/submissions/47c907c5-f1dc-429a-8e60-8057275a51a1

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

theorem cache_summary_595_oai :
    (denote cache_595).A = {(-1, 0)} ∧
    (denote cache_595).H.card = 222 ∧
    (denote cache_595).height = 27 := by
  decide +kernel

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_summary_595_oai := @OAI.SnakyCertificate.Check.cache_summary_595_oai
