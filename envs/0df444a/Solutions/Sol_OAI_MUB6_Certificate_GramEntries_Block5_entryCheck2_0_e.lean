-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block5.entryCheck2_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:09:42.611529+00:00
-- url     : https://prove2.me/submissions/6beb06c5-6bd8-4b02-b308-e74c4a835704

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E035
import Definitions.Def_OAIQ106E041

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block5Row2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block5

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck2_0_e_oai : entry2_0 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block5.form2.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block5.form2.terms k).coefficient) (rows2_0 k)) := by decide +kernel

end MUB6.Certificate.GramEntries.Block5

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block5.entryCheck2_0_e_oai := @OAI.MUB6.Certificate.GramEntries.Block5.entryCheck2_0_e_oai
