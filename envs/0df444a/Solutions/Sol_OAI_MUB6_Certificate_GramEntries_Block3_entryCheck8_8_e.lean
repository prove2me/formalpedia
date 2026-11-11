-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryCheck8_8_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:08:53.299173+00:00
-- url     : https://prove2.me/submissions/8dd6a8f5-04df-4ee3-8470-b895c6631b32

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E025
import Definitions.Def_OAIQ106E034

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck8_8_e_oai : entry8_8 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form8.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form8.terms k).coefficient) (rows8_8 k)) := by decide +kernel

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryCheck8_8_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryCheck8_8_e_oai
