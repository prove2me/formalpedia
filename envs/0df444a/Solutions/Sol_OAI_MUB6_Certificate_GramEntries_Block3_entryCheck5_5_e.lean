-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramEntries.Block3.entryCheck5_5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T13:08:50.393006+00:00
-- url     : https://prove2.me/submissions/3abbef47-4fc7-4c25-9b43-017597480606

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E025
import Definitions.Def_OAIQ106E031

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramEntries_Block3Row5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramEntries.Block3

open GramRows GramNormalization GramPolynomial
open scoped BigOperators

theorem entryCheck5_5_e_oai : entry5_5 =
    Integer.Sparse.collectLevels keyLess GramFunctions.Block3.form5.size
      (List.ofFn fun k => Integer.Sparse.scale ((GramFunctions.Block3.form5.terms k).coefficient) (rows5_5 k)) := by decide +kernel

end MUB6.Certificate.GramEntries.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramEntries.Block3.entryCheck5_5_e_oai := @OAI.MUB6.Certificate.GramEntries.Block3.entryCheck5_5_e_oai
