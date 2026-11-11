-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryCheck9_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:08:57.31399+00:00
-- url     : https://prove2.me/submissions/da2c6e42-c91f-43d6-83b7-2bdb290a3444

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E025
import Definitions.Def_OAIQ106E033

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck9_5_e_oai : entry9_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form9.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form9.terms k).coefficient) (rows9_5 k)) := by decide +kernel

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryCheck9_5_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryCheck9_5_e_oai
