-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block0.entryCheck3_1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T12:58:10.241201+00:00
-- url     : https://prove2.me/submissions/b4caa3ac-d387-4171-af87-6697da249037

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E014

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block0Row3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block0

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck3_1_e_oai : entry3_1 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block0.form3.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block0.form3.terms k).coefficient) (rows3_1 k)) := by decide +kernel

end MUB6.Certificate.GramEntries.Block0

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block0.entryCheck3_1_e_oai := @OAI.MUB6.Certificate.GramEntries.Block0.entryCheck3_1_e_oai
