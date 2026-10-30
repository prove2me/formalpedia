-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_summary_557
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T00:02:38.676754+00:00
-- url     : https://prove2.me/submissions/b0af9034-5715-4924-b6a0-32106aaf9428

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

theorem cache_summary_557_oai :
    (denote cache_557).A = {(-1, 0)} ∧
    (denote cache_557).H.card = 118 ∧
    (denote cache_557).height = 19 := by
  decide +kernel

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_summary_557_oai := @OAI.SnakyCertificate.Check.cache_summary_557_oai
