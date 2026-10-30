-- Prove2me | solution 1 for OAI.SnakyCertificate.Check.cache_summary_603
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T00:03:24.151728+00:00
-- url     : https://prove2.me/submissions/181d5392-bc83-4d22-a85c-1652b8aa8cbe

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

theorem cache_summary_603_oai :
    (denote cache_603).A = {(-1, 0)} ∧
    (denote cache_603).H.card = 275 ∧
    (denote cache_603).height = 27 := by
  decide +kernel

end SnakyCertificate.Check

end OAI
end

theorem solution : type_of% @OAI.SnakyCertificate.Check.cache_summary_603_oai := @OAI.SnakyCertificate.Check.cache_summary_603_oai
