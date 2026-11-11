-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-09T03:19:25.100878+00:00
-- url     : https://prove2.me/submissions/9305716d-b9fd-4554-964b-987aa1033966

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_MUBSix
import Definitions.Def_OAIQ106E005
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E028
import Definitions.Def_OAIQ106E042
import Definitions.Def_OAIQ106E043
import Definitions.Def_OAIQ106E151
import Theorems.Thm_OAI_MUB6_Certificate_GramAssembly_Block3_polynomial_eval_e
import Theorems.Thm_OAI_MUB6_Certificate_GramEntries_Block3_entryEval_e

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

open scoped BigOperators

theorem weights_cast_0 (j : Fin 27) :
    (weights 0 j : ℚ) = GramData.Block3.Z 0 j := by
  revert j
  decide +kernel

theorem weights_cast_1 (j : Fin 27) :
    (weights 1 j : ℚ) = GramData.Block3.Z 1 j := by
  revert j
  decide +kernel

theorem weights_cast_2 (j : Fin 27) :
    (weights 2 j : ℚ) = GramData.Block3.Z 2 j := by
  revert j
  decide +kernel

theorem weights_cast_3 (j : Fin 27) :
    (weights 3 j : ℚ) = GramData.Block3.Z 3 j := by
  revert j
  decide +kernel

theorem weights_cast_4 (j : Fin 27) :
    (weights 4 j : ℚ) = GramData.Block3.Z 4 j := by
  revert j
  decide +kernel

theorem weights_cast_5 (j : Fin 27) :
    (weights 5 j : ℚ) = GramData.Block3.Z 5 j := by
  revert j
  decide +kernel

theorem weights_cast_6 (j : Fin 27) :
    (weights 6 j : ℚ) = GramData.Block3.Z 6 j := by
  revert j
  decide +kernel

theorem weights_cast_7 (j : Fin 27) :
    (weights 7 j : ℚ) = GramData.Block3.Z 7 j := by
  revert j
  decide +kernel

theorem weights_cast_8 (j : Fin 27) :
    (weights 8 j : ℚ) = GramData.Block3.Z 8 j := by
  revert j
  decide +kernel

theorem weights_cast_9 (j : Fin 27) :
    (weights 9 j : ℚ) = GramData.Block3.Z 9 j := by
  revert j
  decide +kernel

theorem weights_cast_10 (j : Fin 27) :
    (weights 10 j : ℚ) = GramData.Block3.Z 10 j := by
  revert j
  decide +kernel

theorem weights_cast_11 (j : Fin 27) :
    (weights 11 j : ℚ) = GramData.Block3.Z 11 j := by
  revert j
  decide +kernel

theorem weights_cast_12 (j : Fin 27) :
    (weights 12 j : ℚ) = GramData.Block3.Z 12 j := by
  revert j
  decide +kernel

theorem weights_cast_13 (j : Fin 27) :
    (weights 13 j : ℚ) = GramData.Block3.Z 13 j := by
  revert j
  decide +kernel

theorem weights_cast_14 (j : Fin 27) :
    (weights 14 j : ℚ) = GramData.Block3.Z 14 j := by
  revert j
  decide +kernel

theorem weights_cast_15 (j : Fin 27) :
    (weights 15 j : ℚ) = GramData.Block3.Z 15 j := by
  revert j
  decide +kernel

theorem weights_cast_16 (j : Fin 27) :
    (weights 16 j : ℚ) = GramData.Block3.Z 16 j := by
  revert j
  decide +kernel

theorem weights_cast_17 (j : Fin 27) :
    (weights 17 j : ℚ) = GramData.Block3.Z 17 j := by
  revert j
  decide +kernel

theorem weights_cast_18 (j : Fin 27) :
    (weights 18 j : ℚ) = GramData.Block3.Z 18 j := by
  revert j
  decide +kernel

theorem weights_cast_19 (j : Fin 27) :
    (weights 19 j : ℚ) = GramData.Block3.Z 19 j := by
  revert j
  decide +kernel

theorem weights_cast_20 (j : Fin 27) :
    (weights 20 j : ℚ) = GramData.Block3.Z 20 j := by
  revert j
  decide +kernel

theorem weights_cast_21 (j : Fin 27) :
    (weights 21 j : ℚ) = GramData.Block3.Z 21 j := by
  revert j
  decide +kernel

theorem weights_cast_22 (j : Fin 27) :
    (weights 22 j : ℚ) = GramData.Block3.Z 22 j := by
  revert j
  decide +kernel

theorem weights_cast_23 (j : Fin 27) :
    (weights 23 j : ℚ) = GramData.Block3.Z 23 j := by
  revert j
  decide +kernel

theorem weights_cast_24 (j : Fin 27) :
    (weights 24 j : ℚ) = GramData.Block3.Z 24 j := by
  revert j
  decide +kernel

theorem weights_cast_25 (j : Fin 27) :
    (weights 25 j : ℚ) = GramData.Block3.Z 25 j := by
  revert j
  decide +kernel

theorem weights_cast_26 (j : Fin 27) :
    (weights 26 j : ℚ) = GramData.Block3.Z 26 j := by
  revert j
  decide +kernel

theorem weights_cast (i j : Fin 27) :
    (weights i j : ℚ) = GramData.Block3.Z i j := by
  fin_cases i
  · exact weights_cast_0 j
  · exact weights_cast_1 j
  · exact weights_cast_2 j
  · exact weights_cast_3 j
  · exact weights_cast_4 j
  · exact weights_cast_5 j
  · exact weights_cast_6 j
  · exact weights_cast_7 j
  · exact weights_cast_8 j
  · exact weights_cast_9 j
  · exact weights_cast_10 j
  · exact weights_cast_11 j
  · exact weights_cast_12 j
  · exact weights_cast_13 j
  · exact weights_cast_14 j
  · exact weights_cast_15 j
  · exact weights_cast_16 j
  · exact weights_cast_17 j
  · exact weights_cast_18 j
  · exact weights_cast_19 j
  · exact weights_cast_20 j
  · exact weights_cast_21 j
  · exact weights_cast_22 j
  · exact weights_cast_23 j
  · exact weights_cast_24 j
  · exact weights_cast_25 j
  · exact weights_cast_26 j

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_0_0 :
    Integer.Sparse.reindex key entry_0_0 = GramEntries.Block3.entries 0 0 := by
  decide +kernel

theorem entry_reindex_0_1 :
    Integer.Sparse.reindex key entry_0_1 = GramEntries.Block3.entries 0 1 := by
  decide +kernel

theorem entry_reindex_0_2 :
    Integer.Sparse.reindex key entry_0_2 = GramEntries.Block3.entries 0 2 := by
  decide +kernel

theorem entry_reindex_0_3 :
    Integer.Sparse.reindex key entry_0_3 = GramEntries.Block3.entries 0 3 := by
  decide +kernel

theorem entry_reindex_0_4 :
    Integer.Sparse.reindex key entry_0_4 = GramEntries.Block3.entries 0 4 := by
  decide +kernel

theorem entry_reindex_0_5 :
    Integer.Sparse.reindex key entry_0_5 = GramEntries.Block3.entries 0 5 := by
  decide +kernel

theorem entry_reindex_0_6 :
    Integer.Sparse.reindex key entry_0_6 = GramEntries.Block3.entries 0 6 := by
  decide +kernel

theorem entry_reindex_0_7 :
    Integer.Sparse.reindex key entry_0_7 = GramEntries.Block3.entries 0 7 := by
  decide +kernel

theorem entry_reindex_0_8 :
    Integer.Sparse.reindex key entry_0_8 = GramEntries.Block3.entries 0 8 := by
  decide +kernel

theorem entry_reindex_0_9 :
    Integer.Sparse.reindex key entry_0_9 = GramEntries.Block3.entries 0 9 := by
  decide +kernel

theorem entry_reindex_0_10 :
    Integer.Sparse.reindex key entry_0_10 = GramEntries.Block3.entries 0 10 := by
  decide +kernel

theorem entry_reindex_0_11 :
    Integer.Sparse.reindex key entry_0_11 = GramEntries.Block3.entries 0 11 := by
  decide +kernel

theorem entry_reindex_0_12 :
    Integer.Sparse.reindex key entry_0_12 = GramEntries.Block3.entries 0 12 := by
  decide +kernel

theorem entry_reindex_0_13 :
    Integer.Sparse.reindex key entry_0_13 = GramEntries.Block3.entries 0 13 := by
  decide +kernel

theorem entry_reindex_0_14 :
    Integer.Sparse.reindex key entry_0_14 = GramEntries.Block3.entries 0 14 := by
  decide +kernel

theorem entry_reindex_0_15 :
    Integer.Sparse.reindex key entry_0_15 = GramEntries.Block3.entries 0 15 := by
  decide +kernel

theorem entry_reindex_0_16 :
    Integer.Sparse.reindex key entry_0_16 = GramEntries.Block3.entries 0 16 := by
  decide +kernel

theorem entry_reindex_0_17 :
    Integer.Sparse.reindex key entry_0_17 = GramEntries.Block3.entries 0 17 := by
  decide +kernel

theorem entry_reindex_0_18 :
    Integer.Sparse.reindex key entry_0_18 = GramEntries.Block3.entries 0 18 := by
  decide +kernel

theorem entry_reindex_0_19 :
    Integer.Sparse.reindex key entry_0_19 = GramEntries.Block3.entries 0 19 := by
  decide +kernel

theorem entry_reindex_0_20 :
    Integer.Sparse.reindex key entry_0_20 = GramEntries.Block3.entries 0 20 := by
  decide +kernel

theorem entry_reindex_0_21 :
    Integer.Sparse.reindex key entry_0_21 = GramEntries.Block3.entries 0 21 := by
  decide +kernel

theorem entry_reindex_0_22 :
    Integer.Sparse.reindex key entry_0_22 = GramEntries.Block3.entries 0 22 := by
  decide +kernel

theorem entry_reindex_0_23 :
    Integer.Sparse.reindex key entry_0_23 = GramEntries.Block3.entries 0 23 := by
  decide +kernel

theorem entry_reindex_0_24 :
    Integer.Sparse.reindex key entry_0_24 = GramEntries.Block3.entries 0 24 := by
  decide +kernel

theorem entry_reindex_0_25 :
    Integer.Sparse.reindex key entry_0_25 = GramEntries.Block3.entries 0 25 := by
  decide +kernel

theorem entry_reindex_0_26 :
    Integer.Sparse.reindex key entry_0_26 = GramEntries.Block3.entries 0 26 := by
  decide +kernel

theorem entries_reindex_0 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 0 j) = GramEntries.Block3.entries 0 j := by
  fin_cases j
  · exact entry_reindex_0_0
  · exact entry_reindex_0_1
  · exact entry_reindex_0_2
  · exact entry_reindex_0_3
  · exact entry_reindex_0_4
  · exact entry_reindex_0_5
  · exact entry_reindex_0_6
  · exact entry_reindex_0_7
  · exact entry_reindex_0_8
  · exact entry_reindex_0_9
  · exact entry_reindex_0_10
  · exact entry_reindex_0_11
  · exact entry_reindex_0_12
  · exact entry_reindex_0_13
  · exact entry_reindex_0_14
  · exact entry_reindex_0_15
  · exact entry_reindex_0_16
  · exact entry_reindex_0_17
  · exact entry_reindex_0_18
  · exact entry_reindex_0_19
  · exact entry_reindex_0_20
  · exact entry_reindex_0_21
  · exact entry_reindex_0_22
  · exact entry_reindex_0_23
  · exact entry_reindex_0_24
  · exact entry_reindex_0_25
  · exact entry_reindex_0_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_1_0 :
    Integer.Sparse.reindex key entry_1_0 = GramEntries.Block3.entries 1 0 := by
  decide +kernel

theorem entry_reindex_1_1 :
    Integer.Sparse.reindex key entry_1_1 = GramEntries.Block3.entries 1 1 := by
  decide +kernel

theorem entry_reindex_1_2 :
    Integer.Sparse.reindex key entry_1_2 = GramEntries.Block3.entries 1 2 := by
  decide +kernel

theorem entry_reindex_1_3 :
    Integer.Sparse.reindex key entry_1_3 = GramEntries.Block3.entries 1 3 := by
  decide +kernel

theorem entry_reindex_1_4 :
    Integer.Sparse.reindex key entry_1_4 = GramEntries.Block3.entries 1 4 := by
  decide +kernel

theorem entry_reindex_1_5 :
    Integer.Sparse.reindex key entry_1_5 = GramEntries.Block3.entries 1 5 := by
  decide +kernel

theorem entry_reindex_1_6 :
    Integer.Sparse.reindex key entry_1_6 = GramEntries.Block3.entries 1 6 := by
  decide +kernel

theorem entry_reindex_1_7 :
    Integer.Sparse.reindex key entry_1_7 = GramEntries.Block3.entries 1 7 := by
  decide +kernel

theorem entry_reindex_1_8 :
    Integer.Sparse.reindex key entry_1_8 = GramEntries.Block3.entries 1 8 := by
  decide +kernel

theorem entry_reindex_1_9 :
    Integer.Sparse.reindex key entry_1_9 = GramEntries.Block3.entries 1 9 := by
  decide +kernel

theorem entry_reindex_1_10 :
    Integer.Sparse.reindex key entry_1_10 = GramEntries.Block3.entries 1 10 := by
  decide +kernel

theorem entry_reindex_1_11 :
    Integer.Sparse.reindex key entry_1_11 = GramEntries.Block3.entries 1 11 := by
  decide +kernel

theorem entry_reindex_1_12 :
    Integer.Sparse.reindex key entry_1_12 = GramEntries.Block3.entries 1 12 := by
  decide +kernel

theorem entry_reindex_1_13 :
    Integer.Sparse.reindex key entry_1_13 = GramEntries.Block3.entries 1 13 := by
  decide +kernel

theorem entry_reindex_1_14 :
    Integer.Sparse.reindex key entry_1_14 = GramEntries.Block3.entries 1 14 := by
  decide +kernel

theorem entry_reindex_1_15 :
    Integer.Sparse.reindex key entry_1_15 = GramEntries.Block3.entries 1 15 := by
  decide +kernel

theorem entry_reindex_1_16 :
    Integer.Sparse.reindex key entry_1_16 = GramEntries.Block3.entries 1 16 := by
  decide +kernel

theorem entry_reindex_1_17 :
    Integer.Sparse.reindex key entry_1_17 = GramEntries.Block3.entries 1 17 := by
  decide +kernel

theorem entry_reindex_1_18 :
    Integer.Sparse.reindex key entry_1_18 = GramEntries.Block3.entries 1 18 := by
  decide +kernel

theorem entry_reindex_1_19 :
    Integer.Sparse.reindex key entry_1_19 = GramEntries.Block3.entries 1 19 := by
  decide +kernel

theorem entry_reindex_1_20 :
    Integer.Sparse.reindex key entry_1_20 = GramEntries.Block3.entries 1 20 := by
  decide +kernel

theorem entry_reindex_1_21 :
    Integer.Sparse.reindex key entry_1_21 = GramEntries.Block3.entries 1 21 := by
  decide +kernel

theorem entry_reindex_1_22 :
    Integer.Sparse.reindex key entry_1_22 = GramEntries.Block3.entries 1 22 := by
  decide +kernel

theorem entry_reindex_1_23 :
    Integer.Sparse.reindex key entry_1_23 = GramEntries.Block3.entries 1 23 := by
  decide +kernel

theorem entry_reindex_1_24 :
    Integer.Sparse.reindex key entry_1_24 = GramEntries.Block3.entries 1 24 := by
  decide +kernel

theorem entry_reindex_1_25 :
    Integer.Sparse.reindex key entry_1_25 = GramEntries.Block3.entries 1 25 := by
  decide +kernel

theorem entry_reindex_1_26 :
    Integer.Sparse.reindex key entry_1_26 = GramEntries.Block3.entries 1 26 := by
  decide +kernel

theorem entries_reindex_1 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 1 j) = GramEntries.Block3.entries 1 j := by
  fin_cases j
  · exact entry_reindex_1_0
  · exact entry_reindex_1_1
  · exact entry_reindex_1_2
  · exact entry_reindex_1_3
  · exact entry_reindex_1_4
  · exact entry_reindex_1_5
  · exact entry_reindex_1_6
  · exact entry_reindex_1_7
  · exact entry_reindex_1_8
  · exact entry_reindex_1_9
  · exact entry_reindex_1_10
  · exact entry_reindex_1_11
  · exact entry_reindex_1_12
  · exact entry_reindex_1_13
  · exact entry_reindex_1_14
  · exact entry_reindex_1_15
  · exact entry_reindex_1_16
  · exact entry_reindex_1_17
  · exact entry_reindex_1_18
  · exact entry_reindex_1_19
  · exact entry_reindex_1_20
  · exact entry_reindex_1_21
  · exact entry_reindex_1_22
  · exact entry_reindex_1_23
  · exact entry_reindex_1_24
  · exact entry_reindex_1_25
  · exact entry_reindex_1_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_10_0 :
    Integer.Sparse.reindex key entry_10_0 = GramEntries.Block3.entries 10 0 := by
  decide +kernel

theorem entry_reindex_10_1 :
    Integer.Sparse.reindex key entry_10_1 = GramEntries.Block3.entries 10 1 := by
  decide +kernel

theorem entry_reindex_10_2 :
    Integer.Sparse.reindex key entry_10_2 = GramEntries.Block3.entries 10 2 := by
  decide +kernel

theorem entry_reindex_10_3 :
    Integer.Sparse.reindex key entry_10_3 = GramEntries.Block3.entries 10 3 := by
  decide +kernel

theorem entry_reindex_10_4 :
    Integer.Sparse.reindex key entry_10_4 = GramEntries.Block3.entries 10 4 := by
  decide +kernel

theorem entry_reindex_10_5 :
    Integer.Sparse.reindex key entry_10_5 = GramEntries.Block3.entries 10 5 := by
  decide +kernel

theorem entry_reindex_10_6 :
    Integer.Sparse.reindex key entry_10_6 = GramEntries.Block3.entries 10 6 := by
  decide +kernel

theorem entry_reindex_10_7 :
    Integer.Sparse.reindex key entry_10_7 = GramEntries.Block3.entries 10 7 := by
  decide +kernel

theorem entry_reindex_10_8 :
    Integer.Sparse.reindex key entry_10_8 = GramEntries.Block3.entries 10 8 := by
  decide +kernel

theorem entry_reindex_10_9 :
    Integer.Sparse.reindex key entry_10_9 = GramEntries.Block3.entries 10 9 := by
  decide +kernel

theorem entry_reindex_10_10 :
    Integer.Sparse.reindex key entry_10_10 = GramEntries.Block3.entries 10 10 := by
  decide +kernel

theorem entry_reindex_10_11 :
    Integer.Sparse.reindex key entry_10_11 = GramEntries.Block3.entries 10 11 := by
  decide +kernel

theorem entry_reindex_10_12 :
    Integer.Sparse.reindex key entry_10_12 = GramEntries.Block3.entries 10 12 := by
  decide +kernel

theorem entry_reindex_10_13 :
    Integer.Sparse.reindex key entry_10_13 = GramEntries.Block3.entries 10 13 := by
  decide +kernel

theorem entry_reindex_10_14 :
    Integer.Sparse.reindex key entry_10_14 = GramEntries.Block3.entries 10 14 := by
  decide +kernel

theorem entry_reindex_10_15 :
    Integer.Sparse.reindex key entry_10_15 = GramEntries.Block3.entries 10 15 := by
  decide +kernel

theorem entry_reindex_10_16 :
    Integer.Sparse.reindex key entry_10_16 = GramEntries.Block3.entries 10 16 := by
  decide +kernel

theorem entry_reindex_10_17 :
    Integer.Sparse.reindex key entry_10_17 = GramEntries.Block3.entries 10 17 := by
  decide +kernel

theorem entry_reindex_10_18 :
    Integer.Sparse.reindex key entry_10_18 = GramEntries.Block3.entries 10 18 := by
  decide +kernel

theorem entry_reindex_10_19 :
    Integer.Sparse.reindex key entry_10_19 = GramEntries.Block3.entries 10 19 := by
  decide +kernel

theorem entry_reindex_10_20 :
    Integer.Sparse.reindex key entry_10_20 = GramEntries.Block3.entries 10 20 := by
  decide +kernel

theorem entry_reindex_10_21 :
    Integer.Sparse.reindex key entry_10_21 = GramEntries.Block3.entries 10 21 := by
  decide +kernel

theorem entry_reindex_10_22 :
    Integer.Sparse.reindex key entry_10_22 = GramEntries.Block3.entries 10 22 := by
  decide +kernel

theorem entry_reindex_10_23 :
    Integer.Sparse.reindex key entry_10_23 = GramEntries.Block3.entries 10 23 := by
  decide +kernel

theorem entry_reindex_10_24 :
    Integer.Sparse.reindex key entry_10_24 = GramEntries.Block3.entries 10 24 := by
  decide +kernel

theorem entry_reindex_10_25 :
    Integer.Sparse.reindex key entry_10_25 = GramEntries.Block3.entries 10 25 := by
  decide +kernel

theorem entry_reindex_10_26 :
    Integer.Sparse.reindex key entry_10_26 = GramEntries.Block3.entries 10 26 := by
  decide +kernel

theorem entries_reindex_10 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 10 j) = GramEntries.Block3.entries 10 j := by
  fin_cases j
  · exact entry_reindex_10_0
  · exact entry_reindex_10_1
  · exact entry_reindex_10_2
  · exact entry_reindex_10_3
  · exact entry_reindex_10_4
  · exact entry_reindex_10_5
  · exact entry_reindex_10_6
  · exact entry_reindex_10_7
  · exact entry_reindex_10_8
  · exact entry_reindex_10_9
  · exact entry_reindex_10_10
  · exact entry_reindex_10_11
  · exact entry_reindex_10_12
  · exact entry_reindex_10_13
  · exact entry_reindex_10_14
  · exact entry_reindex_10_15
  · exact entry_reindex_10_16
  · exact entry_reindex_10_17
  · exact entry_reindex_10_18
  · exact entry_reindex_10_19
  · exact entry_reindex_10_20
  · exact entry_reindex_10_21
  · exact entry_reindex_10_22
  · exact entry_reindex_10_23
  · exact entry_reindex_10_24
  · exact entry_reindex_10_25
  · exact entry_reindex_10_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_11_0 :
    Integer.Sparse.reindex key entry_11_0 = GramEntries.Block3.entries 11 0 := by
  decide +kernel

theorem entry_reindex_11_1 :
    Integer.Sparse.reindex key entry_11_1 = GramEntries.Block3.entries 11 1 := by
  decide +kernel

theorem entry_reindex_11_2 :
    Integer.Sparse.reindex key entry_11_2 = GramEntries.Block3.entries 11 2 := by
  decide +kernel

theorem entry_reindex_11_3 :
    Integer.Sparse.reindex key entry_11_3 = GramEntries.Block3.entries 11 3 := by
  decide +kernel

theorem entry_reindex_11_4 :
    Integer.Sparse.reindex key entry_11_4 = GramEntries.Block3.entries 11 4 := by
  decide +kernel

theorem entry_reindex_11_5 :
    Integer.Sparse.reindex key entry_11_5 = GramEntries.Block3.entries 11 5 := by
  decide +kernel

theorem entry_reindex_11_6 :
    Integer.Sparse.reindex key entry_11_6 = GramEntries.Block3.entries 11 6 := by
  decide +kernel

theorem entry_reindex_11_7 :
    Integer.Sparse.reindex key entry_11_7 = GramEntries.Block3.entries 11 7 := by
  decide +kernel

theorem entry_reindex_11_8 :
    Integer.Sparse.reindex key entry_11_8 = GramEntries.Block3.entries 11 8 := by
  decide +kernel

theorem entry_reindex_11_9 :
    Integer.Sparse.reindex key entry_11_9 = GramEntries.Block3.entries 11 9 := by
  decide +kernel

theorem entry_reindex_11_10 :
    Integer.Sparse.reindex key entry_11_10 = GramEntries.Block3.entries 11 10 := by
  decide +kernel

theorem entry_reindex_11_11 :
    Integer.Sparse.reindex key entry_11_11 = GramEntries.Block3.entries 11 11 := by
  decide +kernel

theorem entry_reindex_11_12 :
    Integer.Sparse.reindex key entry_11_12 = GramEntries.Block3.entries 11 12 := by
  decide +kernel

theorem entry_reindex_11_13 :
    Integer.Sparse.reindex key entry_11_13 = GramEntries.Block3.entries 11 13 := by
  decide +kernel

theorem entry_reindex_11_14 :
    Integer.Sparse.reindex key entry_11_14 = GramEntries.Block3.entries 11 14 := by
  decide +kernel

theorem entry_reindex_11_15 :
    Integer.Sparse.reindex key entry_11_15 = GramEntries.Block3.entries 11 15 := by
  decide +kernel

theorem entry_reindex_11_16 :
    Integer.Sparse.reindex key entry_11_16 = GramEntries.Block3.entries 11 16 := by
  decide +kernel

theorem entry_reindex_11_17 :
    Integer.Sparse.reindex key entry_11_17 = GramEntries.Block3.entries 11 17 := by
  decide +kernel

theorem entry_reindex_11_18 :
    Integer.Sparse.reindex key entry_11_18 = GramEntries.Block3.entries 11 18 := by
  decide +kernel

theorem entry_reindex_11_19 :
    Integer.Sparse.reindex key entry_11_19 = GramEntries.Block3.entries 11 19 := by
  decide +kernel

theorem entry_reindex_11_20 :
    Integer.Sparse.reindex key entry_11_20 = GramEntries.Block3.entries 11 20 := by
  decide +kernel

theorem entry_reindex_11_21 :
    Integer.Sparse.reindex key entry_11_21 = GramEntries.Block3.entries 11 21 := by
  decide +kernel

theorem entry_reindex_11_22 :
    Integer.Sparse.reindex key entry_11_22 = GramEntries.Block3.entries 11 22 := by
  decide +kernel

theorem entry_reindex_11_23 :
    Integer.Sparse.reindex key entry_11_23 = GramEntries.Block3.entries 11 23 := by
  decide +kernel

theorem entry_reindex_11_24 :
    Integer.Sparse.reindex key entry_11_24 = GramEntries.Block3.entries 11 24 := by
  decide +kernel

theorem entry_reindex_11_25 :
    Integer.Sparse.reindex key entry_11_25 = GramEntries.Block3.entries 11 25 := by
  decide +kernel

theorem entry_reindex_11_26 :
    Integer.Sparse.reindex key entry_11_26 = GramEntries.Block3.entries 11 26 := by
  decide +kernel

theorem entries_reindex_11 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 11 j) = GramEntries.Block3.entries 11 j := by
  fin_cases j
  · exact entry_reindex_11_0
  · exact entry_reindex_11_1
  · exact entry_reindex_11_2
  · exact entry_reindex_11_3
  · exact entry_reindex_11_4
  · exact entry_reindex_11_5
  · exact entry_reindex_11_6
  · exact entry_reindex_11_7
  · exact entry_reindex_11_8
  · exact entry_reindex_11_9
  · exact entry_reindex_11_10
  · exact entry_reindex_11_11
  · exact entry_reindex_11_12
  · exact entry_reindex_11_13
  · exact entry_reindex_11_14
  · exact entry_reindex_11_15
  · exact entry_reindex_11_16
  · exact entry_reindex_11_17
  · exact entry_reindex_11_18
  · exact entry_reindex_11_19
  · exact entry_reindex_11_20
  · exact entry_reindex_11_21
  · exact entry_reindex_11_22
  · exact entry_reindex_11_23
  · exact entry_reindex_11_24
  · exact entry_reindex_11_25
  · exact entry_reindex_11_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_12_0 :
    Integer.Sparse.reindex key entry_12_0 = GramEntries.Block3.entries 12 0 := by
  decide +kernel

theorem entry_reindex_12_1 :
    Integer.Sparse.reindex key entry_12_1 = GramEntries.Block3.entries 12 1 := by
  decide +kernel

theorem entry_reindex_12_2 :
    Integer.Sparse.reindex key entry_12_2 = GramEntries.Block3.entries 12 2 := by
  decide +kernel

theorem entry_reindex_12_3 :
    Integer.Sparse.reindex key entry_12_3 = GramEntries.Block3.entries 12 3 := by
  decide +kernel

theorem entry_reindex_12_4 :
    Integer.Sparse.reindex key entry_12_4 = GramEntries.Block3.entries 12 4 := by
  decide +kernel

theorem entry_reindex_12_5 :
    Integer.Sparse.reindex key entry_12_5 = GramEntries.Block3.entries 12 5 := by
  decide +kernel

theorem entry_reindex_12_6 :
    Integer.Sparse.reindex key entry_12_6 = GramEntries.Block3.entries 12 6 := by
  decide +kernel

theorem entry_reindex_12_7 :
    Integer.Sparse.reindex key entry_12_7 = GramEntries.Block3.entries 12 7 := by
  decide +kernel

theorem entry_reindex_12_8 :
    Integer.Sparse.reindex key entry_12_8 = GramEntries.Block3.entries 12 8 := by
  decide +kernel

theorem entry_reindex_12_9 :
    Integer.Sparse.reindex key entry_12_9 = GramEntries.Block3.entries 12 9 := by
  decide +kernel

theorem entry_reindex_12_10 :
    Integer.Sparse.reindex key entry_12_10 = GramEntries.Block3.entries 12 10 := by
  decide +kernel

theorem entry_reindex_12_11 :
    Integer.Sparse.reindex key entry_12_11 = GramEntries.Block3.entries 12 11 := by
  decide +kernel

theorem entry_reindex_12_12 :
    Integer.Sparse.reindex key entry_12_12 = GramEntries.Block3.entries 12 12 := by
  decide +kernel

theorem entry_reindex_12_13 :
    Integer.Sparse.reindex key entry_12_13 = GramEntries.Block3.entries 12 13 := by
  decide +kernel

theorem entry_reindex_12_14 :
    Integer.Sparse.reindex key entry_12_14 = GramEntries.Block3.entries 12 14 := by
  decide +kernel

theorem entry_reindex_12_15 :
    Integer.Sparse.reindex key entry_12_15 = GramEntries.Block3.entries 12 15 := by
  decide +kernel

theorem entry_reindex_12_16 :
    Integer.Sparse.reindex key entry_12_16 = GramEntries.Block3.entries 12 16 := by
  decide +kernel

theorem entry_reindex_12_17 :
    Integer.Sparse.reindex key entry_12_17 = GramEntries.Block3.entries 12 17 := by
  decide +kernel

theorem entry_reindex_12_18 :
    Integer.Sparse.reindex key entry_12_18 = GramEntries.Block3.entries 12 18 := by
  decide +kernel

theorem entry_reindex_12_19 :
    Integer.Sparse.reindex key entry_12_19 = GramEntries.Block3.entries 12 19 := by
  decide +kernel

theorem entry_reindex_12_20 :
    Integer.Sparse.reindex key entry_12_20 = GramEntries.Block3.entries 12 20 := by
  decide +kernel

theorem entry_reindex_12_21 :
    Integer.Sparse.reindex key entry_12_21 = GramEntries.Block3.entries 12 21 := by
  decide +kernel

theorem entry_reindex_12_22 :
    Integer.Sparse.reindex key entry_12_22 = GramEntries.Block3.entries 12 22 := by
  decide +kernel

theorem entry_reindex_12_23 :
    Integer.Sparse.reindex key entry_12_23 = GramEntries.Block3.entries 12 23 := by
  decide +kernel

theorem entry_reindex_12_24 :
    Integer.Sparse.reindex key entry_12_24 = GramEntries.Block3.entries 12 24 := by
  decide +kernel

theorem entry_reindex_12_25 :
    Integer.Sparse.reindex key entry_12_25 = GramEntries.Block3.entries 12 25 := by
  decide +kernel

theorem entry_reindex_12_26 :
    Integer.Sparse.reindex key entry_12_26 = GramEntries.Block3.entries 12 26 := by
  decide +kernel

theorem entries_reindex_12 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 12 j) = GramEntries.Block3.entries 12 j := by
  fin_cases j
  · exact entry_reindex_12_0
  · exact entry_reindex_12_1
  · exact entry_reindex_12_2
  · exact entry_reindex_12_3
  · exact entry_reindex_12_4
  · exact entry_reindex_12_5
  · exact entry_reindex_12_6
  · exact entry_reindex_12_7
  · exact entry_reindex_12_8
  · exact entry_reindex_12_9
  · exact entry_reindex_12_10
  · exact entry_reindex_12_11
  · exact entry_reindex_12_12
  · exact entry_reindex_12_13
  · exact entry_reindex_12_14
  · exact entry_reindex_12_15
  · exact entry_reindex_12_16
  · exact entry_reindex_12_17
  · exact entry_reindex_12_18
  · exact entry_reindex_12_19
  · exact entry_reindex_12_20
  · exact entry_reindex_12_21
  · exact entry_reindex_12_22
  · exact entry_reindex_12_23
  · exact entry_reindex_12_24
  · exact entry_reindex_12_25
  · exact entry_reindex_12_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_13_0 :
    Integer.Sparse.reindex key entry_13_0 = GramEntries.Block3.entries 13 0 := by
  decide +kernel

theorem entry_reindex_13_1 :
    Integer.Sparse.reindex key entry_13_1 = GramEntries.Block3.entries 13 1 := by
  decide +kernel

theorem entry_reindex_13_2 :
    Integer.Sparse.reindex key entry_13_2 = GramEntries.Block3.entries 13 2 := by
  decide +kernel

theorem entry_reindex_13_3 :
    Integer.Sparse.reindex key entry_13_3 = GramEntries.Block3.entries 13 3 := by
  decide +kernel

theorem entry_reindex_13_4 :
    Integer.Sparse.reindex key entry_13_4 = GramEntries.Block3.entries 13 4 := by
  decide +kernel

theorem entry_reindex_13_5 :
    Integer.Sparse.reindex key entry_13_5 = GramEntries.Block3.entries 13 5 := by
  decide +kernel

theorem entry_reindex_13_6 :
    Integer.Sparse.reindex key entry_13_6 = GramEntries.Block3.entries 13 6 := by
  decide +kernel

theorem entry_reindex_13_7 :
    Integer.Sparse.reindex key entry_13_7 = GramEntries.Block3.entries 13 7 := by
  decide +kernel

theorem entry_reindex_13_8 :
    Integer.Sparse.reindex key entry_13_8 = GramEntries.Block3.entries 13 8 := by
  decide +kernel

theorem entry_reindex_13_9 :
    Integer.Sparse.reindex key entry_13_9 = GramEntries.Block3.entries 13 9 := by
  decide +kernel

theorem entry_reindex_13_10 :
    Integer.Sparse.reindex key entry_13_10 = GramEntries.Block3.entries 13 10 := by
  decide +kernel

theorem entry_reindex_13_11 :
    Integer.Sparse.reindex key entry_13_11 = GramEntries.Block3.entries 13 11 := by
  decide +kernel

theorem entry_reindex_13_12 :
    Integer.Sparse.reindex key entry_13_12 = GramEntries.Block3.entries 13 12 := by
  decide +kernel

theorem entry_reindex_13_13 :
    Integer.Sparse.reindex key entry_13_13 = GramEntries.Block3.entries 13 13 := by
  decide +kernel

theorem entry_reindex_13_14 :
    Integer.Sparse.reindex key entry_13_14 = GramEntries.Block3.entries 13 14 := by
  decide +kernel

theorem entry_reindex_13_15 :
    Integer.Sparse.reindex key entry_13_15 = GramEntries.Block3.entries 13 15 := by
  decide +kernel

theorem entry_reindex_13_16 :
    Integer.Sparse.reindex key entry_13_16 = GramEntries.Block3.entries 13 16 := by
  decide +kernel

theorem entry_reindex_13_17 :
    Integer.Sparse.reindex key entry_13_17 = GramEntries.Block3.entries 13 17 := by
  decide +kernel

theorem entry_reindex_13_18 :
    Integer.Sparse.reindex key entry_13_18 = GramEntries.Block3.entries 13 18 := by
  decide +kernel

theorem entry_reindex_13_19 :
    Integer.Sparse.reindex key entry_13_19 = GramEntries.Block3.entries 13 19 := by
  decide +kernel

theorem entry_reindex_13_20 :
    Integer.Sparse.reindex key entry_13_20 = GramEntries.Block3.entries 13 20 := by
  decide +kernel

theorem entry_reindex_13_21 :
    Integer.Sparse.reindex key entry_13_21 = GramEntries.Block3.entries 13 21 := by
  decide +kernel

theorem entry_reindex_13_22 :
    Integer.Sparse.reindex key entry_13_22 = GramEntries.Block3.entries 13 22 := by
  decide +kernel

theorem entry_reindex_13_23 :
    Integer.Sparse.reindex key entry_13_23 = GramEntries.Block3.entries 13 23 := by
  decide +kernel

theorem entry_reindex_13_24 :
    Integer.Sparse.reindex key entry_13_24 = GramEntries.Block3.entries 13 24 := by
  decide +kernel

theorem entry_reindex_13_25 :
    Integer.Sparse.reindex key entry_13_25 = GramEntries.Block3.entries 13 25 := by
  decide +kernel

theorem entry_reindex_13_26 :
    Integer.Sparse.reindex key entry_13_26 = GramEntries.Block3.entries 13 26 := by
  decide +kernel

theorem entries_reindex_13 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 13 j) = GramEntries.Block3.entries 13 j := by
  fin_cases j
  · exact entry_reindex_13_0
  · exact entry_reindex_13_1
  · exact entry_reindex_13_2
  · exact entry_reindex_13_3
  · exact entry_reindex_13_4
  · exact entry_reindex_13_5
  · exact entry_reindex_13_6
  · exact entry_reindex_13_7
  · exact entry_reindex_13_8
  · exact entry_reindex_13_9
  · exact entry_reindex_13_10
  · exact entry_reindex_13_11
  · exact entry_reindex_13_12
  · exact entry_reindex_13_13
  · exact entry_reindex_13_14
  · exact entry_reindex_13_15
  · exact entry_reindex_13_16
  · exact entry_reindex_13_17
  · exact entry_reindex_13_18
  · exact entry_reindex_13_19
  · exact entry_reindex_13_20
  · exact entry_reindex_13_21
  · exact entry_reindex_13_22
  · exact entry_reindex_13_23
  · exact entry_reindex_13_24
  · exact entry_reindex_13_25
  · exact entry_reindex_13_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex14
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_14_0 :
    Integer.Sparse.reindex key entry_14_0 = GramEntries.Block3.entries 14 0 := by
  decide +kernel

theorem entry_reindex_14_1 :
    Integer.Sparse.reindex key entry_14_1 = GramEntries.Block3.entries 14 1 := by
  decide +kernel

theorem entry_reindex_14_2 :
    Integer.Sparse.reindex key entry_14_2 = GramEntries.Block3.entries 14 2 := by
  decide +kernel

theorem entry_reindex_14_3 :
    Integer.Sparse.reindex key entry_14_3 = GramEntries.Block3.entries 14 3 := by
  decide +kernel

theorem entry_reindex_14_4 :
    Integer.Sparse.reindex key entry_14_4 = GramEntries.Block3.entries 14 4 := by
  decide +kernel

theorem entry_reindex_14_5 :
    Integer.Sparse.reindex key entry_14_5 = GramEntries.Block3.entries 14 5 := by
  decide +kernel

theorem entry_reindex_14_6 :
    Integer.Sparse.reindex key entry_14_6 = GramEntries.Block3.entries 14 6 := by
  decide +kernel

theorem entry_reindex_14_7 :
    Integer.Sparse.reindex key entry_14_7 = GramEntries.Block3.entries 14 7 := by
  decide +kernel

theorem entry_reindex_14_8 :
    Integer.Sparse.reindex key entry_14_8 = GramEntries.Block3.entries 14 8 := by
  decide +kernel

theorem entry_reindex_14_9 :
    Integer.Sparse.reindex key entry_14_9 = GramEntries.Block3.entries 14 9 := by
  decide +kernel

theorem entry_reindex_14_10 :
    Integer.Sparse.reindex key entry_14_10 = GramEntries.Block3.entries 14 10 := by
  decide +kernel

theorem entry_reindex_14_11 :
    Integer.Sparse.reindex key entry_14_11 = GramEntries.Block3.entries 14 11 := by
  decide +kernel

theorem entry_reindex_14_12 :
    Integer.Sparse.reindex key entry_14_12 = GramEntries.Block3.entries 14 12 := by
  decide +kernel

theorem entry_reindex_14_13 :
    Integer.Sparse.reindex key entry_14_13 = GramEntries.Block3.entries 14 13 := by
  decide +kernel

theorem entry_reindex_14_14 :
    Integer.Sparse.reindex key entry_14_14 = GramEntries.Block3.entries 14 14 := by
  decide +kernel

theorem entry_reindex_14_15 :
    Integer.Sparse.reindex key entry_14_15 = GramEntries.Block3.entries 14 15 := by
  decide +kernel

theorem entry_reindex_14_16 :
    Integer.Sparse.reindex key entry_14_16 = GramEntries.Block3.entries 14 16 := by
  decide +kernel

theorem entry_reindex_14_17 :
    Integer.Sparse.reindex key entry_14_17 = GramEntries.Block3.entries 14 17 := by
  decide +kernel

theorem entry_reindex_14_18 :
    Integer.Sparse.reindex key entry_14_18 = GramEntries.Block3.entries 14 18 := by
  decide +kernel

theorem entry_reindex_14_19 :
    Integer.Sparse.reindex key entry_14_19 = GramEntries.Block3.entries 14 19 := by
  decide +kernel

theorem entry_reindex_14_20 :
    Integer.Sparse.reindex key entry_14_20 = GramEntries.Block3.entries 14 20 := by
  decide +kernel

theorem entry_reindex_14_21 :
    Integer.Sparse.reindex key entry_14_21 = GramEntries.Block3.entries 14 21 := by
  decide +kernel

theorem entry_reindex_14_22 :
    Integer.Sparse.reindex key entry_14_22 = GramEntries.Block3.entries 14 22 := by
  decide +kernel

theorem entry_reindex_14_23 :
    Integer.Sparse.reindex key entry_14_23 = GramEntries.Block3.entries 14 23 := by
  decide +kernel

theorem entry_reindex_14_24 :
    Integer.Sparse.reindex key entry_14_24 = GramEntries.Block3.entries 14 24 := by
  decide +kernel

theorem entry_reindex_14_25 :
    Integer.Sparse.reindex key entry_14_25 = GramEntries.Block3.entries 14 25 := by
  decide +kernel

theorem entry_reindex_14_26 :
    Integer.Sparse.reindex key entry_14_26 = GramEntries.Block3.entries 14 26 := by
  decide +kernel

theorem entries_reindex_14 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 14 j) = GramEntries.Block3.entries 14 j := by
  fin_cases j
  · exact entry_reindex_14_0
  · exact entry_reindex_14_1
  · exact entry_reindex_14_2
  · exact entry_reindex_14_3
  · exact entry_reindex_14_4
  · exact entry_reindex_14_5
  · exact entry_reindex_14_6
  · exact entry_reindex_14_7
  · exact entry_reindex_14_8
  · exact entry_reindex_14_9
  · exact entry_reindex_14_10
  · exact entry_reindex_14_11
  · exact entry_reindex_14_12
  · exact entry_reindex_14_13
  · exact entry_reindex_14_14
  · exact entry_reindex_14_15
  · exact entry_reindex_14_16
  · exact entry_reindex_14_17
  · exact entry_reindex_14_18
  · exact entry_reindex_14_19
  · exact entry_reindex_14_20
  · exact entry_reindex_14_21
  · exact entry_reindex_14_22
  · exact entry_reindex_14_23
  · exact entry_reindex_14_24
  · exact entry_reindex_14_25
  · exact entry_reindex_14_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_15_0 :
    Integer.Sparse.reindex key entry_15_0 = GramEntries.Block3.entries 15 0 := by
  decide +kernel

theorem entry_reindex_15_1 :
    Integer.Sparse.reindex key entry_15_1 = GramEntries.Block3.entries 15 1 := by
  decide +kernel

theorem entry_reindex_15_2 :
    Integer.Sparse.reindex key entry_15_2 = GramEntries.Block3.entries 15 2 := by
  decide +kernel

theorem entry_reindex_15_3 :
    Integer.Sparse.reindex key entry_15_3 = GramEntries.Block3.entries 15 3 := by
  decide +kernel

theorem entry_reindex_15_4 :
    Integer.Sparse.reindex key entry_15_4 = GramEntries.Block3.entries 15 4 := by
  decide +kernel

theorem entry_reindex_15_5 :
    Integer.Sparse.reindex key entry_15_5 = GramEntries.Block3.entries 15 5 := by
  decide +kernel

theorem entry_reindex_15_6 :
    Integer.Sparse.reindex key entry_15_6 = GramEntries.Block3.entries 15 6 := by
  decide +kernel

theorem entry_reindex_15_7 :
    Integer.Sparse.reindex key entry_15_7 = GramEntries.Block3.entries 15 7 := by
  decide +kernel

theorem entry_reindex_15_8 :
    Integer.Sparse.reindex key entry_15_8 = GramEntries.Block3.entries 15 8 := by
  decide +kernel

theorem entry_reindex_15_9 :
    Integer.Sparse.reindex key entry_15_9 = GramEntries.Block3.entries 15 9 := by
  decide +kernel

theorem entry_reindex_15_10 :
    Integer.Sparse.reindex key entry_15_10 = GramEntries.Block3.entries 15 10 := by
  decide +kernel

theorem entry_reindex_15_11 :
    Integer.Sparse.reindex key entry_15_11 = GramEntries.Block3.entries 15 11 := by
  decide +kernel

theorem entry_reindex_15_12 :
    Integer.Sparse.reindex key entry_15_12 = GramEntries.Block3.entries 15 12 := by
  decide +kernel

theorem entry_reindex_15_13 :
    Integer.Sparse.reindex key entry_15_13 = GramEntries.Block3.entries 15 13 := by
  decide +kernel

theorem entry_reindex_15_14 :
    Integer.Sparse.reindex key entry_15_14 = GramEntries.Block3.entries 15 14 := by
  decide +kernel

theorem entry_reindex_15_15 :
    Integer.Sparse.reindex key entry_15_15 = GramEntries.Block3.entries 15 15 := by
  decide +kernel

theorem entry_reindex_15_16 :
    Integer.Sparse.reindex key entry_15_16 = GramEntries.Block3.entries 15 16 := by
  decide +kernel

theorem entry_reindex_15_17 :
    Integer.Sparse.reindex key entry_15_17 = GramEntries.Block3.entries 15 17 := by
  decide +kernel

theorem entry_reindex_15_18 :
    Integer.Sparse.reindex key entry_15_18 = GramEntries.Block3.entries 15 18 := by
  decide +kernel

theorem entry_reindex_15_19 :
    Integer.Sparse.reindex key entry_15_19 = GramEntries.Block3.entries 15 19 := by
  decide +kernel

theorem entry_reindex_15_20 :
    Integer.Sparse.reindex key entry_15_20 = GramEntries.Block3.entries 15 20 := by
  decide +kernel

theorem entry_reindex_15_21 :
    Integer.Sparse.reindex key entry_15_21 = GramEntries.Block3.entries 15 21 := by
  decide +kernel

theorem entry_reindex_15_22 :
    Integer.Sparse.reindex key entry_15_22 = GramEntries.Block3.entries 15 22 := by
  decide +kernel

theorem entry_reindex_15_23 :
    Integer.Sparse.reindex key entry_15_23 = GramEntries.Block3.entries 15 23 := by
  decide +kernel

theorem entry_reindex_15_24 :
    Integer.Sparse.reindex key entry_15_24 = GramEntries.Block3.entries 15 24 := by
  decide +kernel

theorem entry_reindex_15_25 :
    Integer.Sparse.reindex key entry_15_25 = GramEntries.Block3.entries 15 25 := by
  decide +kernel

theorem entry_reindex_15_26 :
    Integer.Sparse.reindex key entry_15_26 = GramEntries.Block3.entries 15 26 := by
  decide +kernel

theorem entries_reindex_15 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 15 j) = GramEntries.Block3.entries 15 j := by
  fin_cases j
  · exact entry_reindex_15_0
  · exact entry_reindex_15_1
  · exact entry_reindex_15_2
  · exact entry_reindex_15_3
  · exact entry_reindex_15_4
  · exact entry_reindex_15_5
  · exact entry_reindex_15_6
  · exact entry_reindex_15_7
  · exact entry_reindex_15_8
  · exact entry_reindex_15_9
  · exact entry_reindex_15_10
  · exact entry_reindex_15_11
  · exact entry_reindex_15_12
  · exact entry_reindex_15_13
  · exact entry_reindex_15_14
  · exact entry_reindex_15_15
  · exact entry_reindex_15_16
  · exact entry_reindex_15_17
  · exact entry_reindex_15_18
  · exact entry_reindex_15_19
  · exact entry_reindex_15_20
  · exact entry_reindex_15_21
  · exact entry_reindex_15_22
  · exact entry_reindex_15_23
  · exact entry_reindex_15_24
  · exact entry_reindex_15_25
  · exact entry_reindex_15_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_16_0 :
    Integer.Sparse.reindex key entry_16_0 = GramEntries.Block3.entries 16 0 := by
  decide +kernel

theorem entry_reindex_16_1 :
    Integer.Sparse.reindex key entry_16_1 = GramEntries.Block3.entries 16 1 := by
  decide +kernel

theorem entry_reindex_16_2 :
    Integer.Sparse.reindex key entry_16_2 = GramEntries.Block3.entries 16 2 := by
  decide +kernel

theorem entry_reindex_16_3 :
    Integer.Sparse.reindex key entry_16_3 = GramEntries.Block3.entries 16 3 := by
  decide +kernel

theorem entry_reindex_16_4 :
    Integer.Sparse.reindex key entry_16_4 = GramEntries.Block3.entries 16 4 := by
  decide +kernel

theorem entry_reindex_16_5 :
    Integer.Sparse.reindex key entry_16_5 = GramEntries.Block3.entries 16 5 := by
  decide +kernel

theorem entry_reindex_16_6 :
    Integer.Sparse.reindex key entry_16_6 = GramEntries.Block3.entries 16 6 := by
  decide +kernel

theorem entry_reindex_16_7 :
    Integer.Sparse.reindex key entry_16_7 = GramEntries.Block3.entries 16 7 := by
  decide +kernel

theorem entry_reindex_16_8 :
    Integer.Sparse.reindex key entry_16_8 = GramEntries.Block3.entries 16 8 := by
  decide +kernel

theorem entry_reindex_16_9 :
    Integer.Sparse.reindex key entry_16_9 = GramEntries.Block3.entries 16 9 := by
  decide +kernel

theorem entry_reindex_16_10 :
    Integer.Sparse.reindex key entry_16_10 = GramEntries.Block3.entries 16 10 := by
  decide +kernel

theorem entry_reindex_16_11 :
    Integer.Sparse.reindex key entry_16_11 = GramEntries.Block3.entries 16 11 := by
  decide +kernel

theorem entry_reindex_16_12 :
    Integer.Sparse.reindex key entry_16_12 = GramEntries.Block3.entries 16 12 := by
  decide +kernel

theorem entry_reindex_16_13 :
    Integer.Sparse.reindex key entry_16_13 = GramEntries.Block3.entries 16 13 := by
  decide +kernel

theorem entry_reindex_16_14 :
    Integer.Sparse.reindex key entry_16_14 = GramEntries.Block3.entries 16 14 := by
  decide +kernel

theorem entry_reindex_16_15 :
    Integer.Sparse.reindex key entry_16_15 = GramEntries.Block3.entries 16 15 := by
  decide +kernel

theorem entry_reindex_16_16 :
    Integer.Sparse.reindex key entry_16_16 = GramEntries.Block3.entries 16 16 := by
  decide +kernel

theorem entry_reindex_16_17 :
    Integer.Sparse.reindex key entry_16_17 = GramEntries.Block3.entries 16 17 := by
  decide +kernel

theorem entry_reindex_16_18 :
    Integer.Sparse.reindex key entry_16_18 = GramEntries.Block3.entries 16 18 := by
  decide +kernel

theorem entry_reindex_16_19 :
    Integer.Sparse.reindex key entry_16_19 = GramEntries.Block3.entries 16 19 := by
  decide +kernel

theorem entry_reindex_16_20 :
    Integer.Sparse.reindex key entry_16_20 = GramEntries.Block3.entries 16 20 := by
  decide +kernel

theorem entry_reindex_16_21 :
    Integer.Sparse.reindex key entry_16_21 = GramEntries.Block3.entries 16 21 := by
  decide +kernel

theorem entry_reindex_16_22 :
    Integer.Sparse.reindex key entry_16_22 = GramEntries.Block3.entries 16 22 := by
  decide +kernel

theorem entry_reindex_16_23 :
    Integer.Sparse.reindex key entry_16_23 = GramEntries.Block3.entries 16 23 := by
  decide +kernel

theorem entry_reindex_16_24 :
    Integer.Sparse.reindex key entry_16_24 = GramEntries.Block3.entries 16 24 := by
  decide +kernel

theorem entry_reindex_16_25 :
    Integer.Sparse.reindex key entry_16_25 = GramEntries.Block3.entries 16 25 := by
  decide +kernel

theorem entry_reindex_16_26 :
    Integer.Sparse.reindex key entry_16_26 = GramEntries.Block3.entries 16 26 := by
  decide +kernel

theorem entries_reindex_16 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 16 j) = GramEntries.Block3.entries 16 j := by
  fin_cases j
  · exact entry_reindex_16_0
  · exact entry_reindex_16_1
  · exact entry_reindex_16_2
  · exact entry_reindex_16_3
  · exact entry_reindex_16_4
  · exact entry_reindex_16_5
  · exact entry_reindex_16_6
  · exact entry_reindex_16_7
  · exact entry_reindex_16_8
  · exact entry_reindex_16_9
  · exact entry_reindex_16_10
  · exact entry_reindex_16_11
  · exact entry_reindex_16_12
  · exact entry_reindex_16_13
  · exact entry_reindex_16_14
  · exact entry_reindex_16_15
  · exact entry_reindex_16_16
  · exact entry_reindex_16_17
  · exact entry_reindex_16_18
  · exact entry_reindex_16_19
  · exact entry_reindex_16_20
  · exact entry_reindex_16_21
  · exact entry_reindex_16_22
  · exact entry_reindex_16_23
  · exact entry_reindex_16_24
  · exact entry_reindex_16_25
  · exact entry_reindex_16_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_17_0 :
    Integer.Sparse.reindex key entry_17_0 = GramEntries.Block3.entries 17 0 := by
  decide +kernel

theorem entry_reindex_17_1 :
    Integer.Sparse.reindex key entry_17_1 = GramEntries.Block3.entries 17 1 := by
  decide +kernel

theorem entry_reindex_17_2 :
    Integer.Sparse.reindex key entry_17_2 = GramEntries.Block3.entries 17 2 := by
  decide +kernel

theorem entry_reindex_17_3 :
    Integer.Sparse.reindex key entry_17_3 = GramEntries.Block3.entries 17 3 := by
  decide +kernel

theorem entry_reindex_17_4 :
    Integer.Sparse.reindex key entry_17_4 = GramEntries.Block3.entries 17 4 := by
  decide +kernel

theorem entry_reindex_17_5 :
    Integer.Sparse.reindex key entry_17_5 = GramEntries.Block3.entries 17 5 := by
  decide +kernel

theorem entry_reindex_17_6 :
    Integer.Sparse.reindex key entry_17_6 = GramEntries.Block3.entries 17 6 := by
  decide +kernel

theorem entry_reindex_17_7 :
    Integer.Sparse.reindex key entry_17_7 = GramEntries.Block3.entries 17 7 := by
  decide +kernel

theorem entry_reindex_17_8 :
    Integer.Sparse.reindex key entry_17_8 = GramEntries.Block3.entries 17 8 := by
  decide +kernel

theorem entry_reindex_17_9 :
    Integer.Sparse.reindex key entry_17_9 = GramEntries.Block3.entries 17 9 := by
  decide +kernel

theorem entry_reindex_17_10 :
    Integer.Sparse.reindex key entry_17_10 = GramEntries.Block3.entries 17 10 := by
  decide +kernel

theorem entry_reindex_17_11 :
    Integer.Sparse.reindex key entry_17_11 = GramEntries.Block3.entries 17 11 := by
  decide +kernel

theorem entry_reindex_17_12 :
    Integer.Sparse.reindex key entry_17_12 = GramEntries.Block3.entries 17 12 := by
  decide +kernel

theorem entry_reindex_17_13 :
    Integer.Sparse.reindex key entry_17_13 = GramEntries.Block3.entries 17 13 := by
  decide +kernel

theorem entry_reindex_17_14 :
    Integer.Sparse.reindex key entry_17_14 = GramEntries.Block3.entries 17 14 := by
  decide +kernel

theorem entry_reindex_17_15 :
    Integer.Sparse.reindex key entry_17_15 = GramEntries.Block3.entries 17 15 := by
  decide +kernel

theorem entry_reindex_17_16 :
    Integer.Sparse.reindex key entry_17_16 = GramEntries.Block3.entries 17 16 := by
  decide +kernel

theorem entry_reindex_17_17 :
    Integer.Sparse.reindex key entry_17_17 = GramEntries.Block3.entries 17 17 := by
  decide +kernel

theorem entry_reindex_17_18 :
    Integer.Sparse.reindex key entry_17_18 = GramEntries.Block3.entries 17 18 := by
  decide +kernel

theorem entry_reindex_17_19 :
    Integer.Sparse.reindex key entry_17_19 = GramEntries.Block3.entries 17 19 := by
  decide +kernel

theorem entry_reindex_17_20 :
    Integer.Sparse.reindex key entry_17_20 = GramEntries.Block3.entries 17 20 := by
  decide +kernel

theorem entry_reindex_17_21 :
    Integer.Sparse.reindex key entry_17_21 = GramEntries.Block3.entries 17 21 := by
  decide +kernel

theorem entry_reindex_17_22 :
    Integer.Sparse.reindex key entry_17_22 = GramEntries.Block3.entries 17 22 := by
  decide +kernel

theorem entry_reindex_17_23 :
    Integer.Sparse.reindex key entry_17_23 = GramEntries.Block3.entries 17 23 := by
  decide +kernel

theorem entry_reindex_17_24 :
    Integer.Sparse.reindex key entry_17_24 = GramEntries.Block3.entries 17 24 := by
  decide +kernel

theorem entry_reindex_17_25 :
    Integer.Sparse.reindex key entry_17_25 = GramEntries.Block3.entries 17 25 := by
  decide +kernel

theorem entry_reindex_17_26 :
    Integer.Sparse.reindex key entry_17_26 = GramEntries.Block3.entries 17 26 := by
  decide +kernel

theorem entries_reindex_17 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 17 j) = GramEntries.Block3.entries 17 j := by
  fin_cases j
  · exact entry_reindex_17_0
  · exact entry_reindex_17_1
  · exact entry_reindex_17_2
  · exact entry_reindex_17_3
  · exact entry_reindex_17_4
  · exact entry_reindex_17_5
  · exact entry_reindex_17_6
  · exact entry_reindex_17_7
  · exact entry_reindex_17_8
  · exact entry_reindex_17_9
  · exact entry_reindex_17_10
  · exact entry_reindex_17_11
  · exact entry_reindex_17_12
  · exact entry_reindex_17_13
  · exact entry_reindex_17_14
  · exact entry_reindex_17_15
  · exact entry_reindex_17_16
  · exact entry_reindex_17_17
  · exact entry_reindex_17_18
  · exact entry_reindex_17_19
  · exact entry_reindex_17_20
  · exact entry_reindex_17_21
  · exact entry_reindex_17_22
  · exact entry_reindex_17_23
  · exact entry_reindex_17_24
  · exact entry_reindex_17_25
  · exact entry_reindex_17_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex18
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_18_0 :
    Integer.Sparse.reindex key entry_18_0 = GramEntries.Block3.entries 18 0 := by
  decide +kernel

theorem entry_reindex_18_1 :
    Integer.Sparse.reindex key entry_18_1 = GramEntries.Block3.entries 18 1 := by
  decide +kernel

theorem entry_reindex_18_2 :
    Integer.Sparse.reindex key entry_18_2 = GramEntries.Block3.entries 18 2 := by
  decide +kernel

theorem entry_reindex_18_3 :
    Integer.Sparse.reindex key entry_18_3 = GramEntries.Block3.entries 18 3 := by
  decide +kernel

theorem entry_reindex_18_4 :
    Integer.Sparse.reindex key entry_18_4 = GramEntries.Block3.entries 18 4 := by
  decide +kernel

theorem entry_reindex_18_5 :
    Integer.Sparse.reindex key entry_18_5 = GramEntries.Block3.entries 18 5 := by
  decide +kernel

theorem entry_reindex_18_6 :
    Integer.Sparse.reindex key entry_18_6 = GramEntries.Block3.entries 18 6 := by
  decide +kernel

theorem entry_reindex_18_7 :
    Integer.Sparse.reindex key entry_18_7 = GramEntries.Block3.entries 18 7 := by
  decide +kernel

theorem entry_reindex_18_8 :
    Integer.Sparse.reindex key entry_18_8 = GramEntries.Block3.entries 18 8 := by
  decide +kernel

theorem entry_reindex_18_9 :
    Integer.Sparse.reindex key entry_18_9 = GramEntries.Block3.entries 18 9 := by
  decide +kernel

theorem entry_reindex_18_10 :
    Integer.Sparse.reindex key entry_18_10 = GramEntries.Block3.entries 18 10 := by
  decide +kernel

theorem entry_reindex_18_11 :
    Integer.Sparse.reindex key entry_18_11 = GramEntries.Block3.entries 18 11 := by
  decide +kernel

theorem entry_reindex_18_12 :
    Integer.Sparse.reindex key entry_18_12 = GramEntries.Block3.entries 18 12 := by
  decide +kernel

theorem entry_reindex_18_13 :
    Integer.Sparse.reindex key entry_18_13 = GramEntries.Block3.entries 18 13 := by
  decide +kernel

theorem entry_reindex_18_14 :
    Integer.Sparse.reindex key entry_18_14 = GramEntries.Block3.entries 18 14 := by
  decide +kernel

theorem entry_reindex_18_15 :
    Integer.Sparse.reindex key entry_18_15 = GramEntries.Block3.entries 18 15 := by
  decide +kernel

theorem entry_reindex_18_16 :
    Integer.Sparse.reindex key entry_18_16 = GramEntries.Block3.entries 18 16 := by
  decide +kernel

theorem entry_reindex_18_17 :
    Integer.Sparse.reindex key entry_18_17 = GramEntries.Block3.entries 18 17 := by
  decide +kernel

theorem entry_reindex_18_18 :
    Integer.Sparse.reindex key entry_18_18 = GramEntries.Block3.entries 18 18 := by
  decide +kernel

theorem entry_reindex_18_19 :
    Integer.Sparse.reindex key entry_18_19 = GramEntries.Block3.entries 18 19 := by
  decide +kernel

theorem entry_reindex_18_20 :
    Integer.Sparse.reindex key entry_18_20 = GramEntries.Block3.entries 18 20 := by
  decide +kernel

theorem entry_reindex_18_21 :
    Integer.Sparse.reindex key entry_18_21 = GramEntries.Block3.entries 18 21 := by
  decide +kernel

theorem entry_reindex_18_22 :
    Integer.Sparse.reindex key entry_18_22 = GramEntries.Block3.entries 18 22 := by
  decide +kernel

theorem entry_reindex_18_23 :
    Integer.Sparse.reindex key entry_18_23 = GramEntries.Block3.entries 18 23 := by
  decide +kernel

theorem entry_reindex_18_24 :
    Integer.Sparse.reindex key entry_18_24 = GramEntries.Block3.entries 18 24 := by
  decide +kernel

theorem entry_reindex_18_25 :
    Integer.Sparse.reindex key entry_18_25 = GramEntries.Block3.entries 18 25 := by
  decide +kernel

theorem entry_reindex_18_26 :
    Integer.Sparse.reindex key entry_18_26 = GramEntries.Block3.entries 18 26 := by
  decide +kernel

theorem entries_reindex_18 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 18 j) = GramEntries.Block3.entries 18 j := by
  fin_cases j
  · exact entry_reindex_18_0
  · exact entry_reindex_18_1
  · exact entry_reindex_18_2
  · exact entry_reindex_18_3
  · exact entry_reindex_18_4
  · exact entry_reindex_18_5
  · exact entry_reindex_18_6
  · exact entry_reindex_18_7
  · exact entry_reindex_18_8
  · exact entry_reindex_18_9
  · exact entry_reindex_18_10
  · exact entry_reindex_18_11
  · exact entry_reindex_18_12
  · exact entry_reindex_18_13
  · exact entry_reindex_18_14
  · exact entry_reindex_18_15
  · exact entry_reindex_18_16
  · exact entry_reindex_18_17
  · exact entry_reindex_18_18
  · exact entry_reindex_18_19
  · exact entry_reindex_18_20
  · exact entry_reindex_18_21
  · exact entry_reindex_18_22
  · exact entry_reindex_18_23
  · exact entry_reindex_18_24
  · exact entry_reindex_18_25
  · exact entry_reindex_18_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_19_0 :
    Integer.Sparse.reindex key entry_19_0 = GramEntries.Block3.entries 19 0 := by
  decide +kernel

theorem entry_reindex_19_1 :
    Integer.Sparse.reindex key entry_19_1 = GramEntries.Block3.entries 19 1 := by
  decide +kernel

theorem entry_reindex_19_2 :
    Integer.Sparse.reindex key entry_19_2 = GramEntries.Block3.entries 19 2 := by
  decide +kernel

theorem entry_reindex_19_3 :
    Integer.Sparse.reindex key entry_19_3 = GramEntries.Block3.entries 19 3 := by
  decide +kernel

theorem entry_reindex_19_4 :
    Integer.Sparse.reindex key entry_19_4 = GramEntries.Block3.entries 19 4 := by
  decide +kernel

theorem entry_reindex_19_5 :
    Integer.Sparse.reindex key entry_19_5 = GramEntries.Block3.entries 19 5 := by
  decide +kernel

theorem entry_reindex_19_6 :
    Integer.Sparse.reindex key entry_19_6 = GramEntries.Block3.entries 19 6 := by
  decide +kernel

theorem entry_reindex_19_7 :
    Integer.Sparse.reindex key entry_19_7 = GramEntries.Block3.entries 19 7 := by
  decide +kernel

theorem entry_reindex_19_8 :
    Integer.Sparse.reindex key entry_19_8 = GramEntries.Block3.entries 19 8 := by
  decide +kernel

theorem entry_reindex_19_9 :
    Integer.Sparse.reindex key entry_19_9 = GramEntries.Block3.entries 19 9 := by
  decide +kernel

theorem entry_reindex_19_10 :
    Integer.Sparse.reindex key entry_19_10 = GramEntries.Block3.entries 19 10 := by
  decide +kernel

theorem entry_reindex_19_11 :
    Integer.Sparse.reindex key entry_19_11 = GramEntries.Block3.entries 19 11 := by
  decide +kernel

theorem entry_reindex_19_12 :
    Integer.Sparse.reindex key entry_19_12 = GramEntries.Block3.entries 19 12 := by
  decide +kernel

theorem entry_reindex_19_13 :
    Integer.Sparse.reindex key entry_19_13 = GramEntries.Block3.entries 19 13 := by
  decide +kernel

theorem entry_reindex_19_14 :
    Integer.Sparse.reindex key entry_19_14 = GramEntries.Block3.entries 19 14 := by
  decide +kernel

theorem entry_reindex_19_15 :
    Integer.Sparse.reindex key entry_19_15 = GramEntries.Block3.entries 19 15 := by
  decide +kernel

theorem entry_reindex_19_16 :
    Integer.Sparse.reindex key entry_19_16 = GramEntries.Block3.entries 19 16 := by
  decide +kernel

theorem entry_reindex_19_17 :
    Integer.Sparse.reindex key entry_19_17 = GramEntries.Block3.entries 19 17 := by
  decide +kernel

theorem entry_reindex_19_18 :
    Integer.Sparse.reindex key entry_19_18 = GramEntries.Block3.entries 19 18 := by
  decide +kernel

theorem entry_reindex_19_19 :
    Integer.Sparse.reindex key entry_19_19 = GramEntries.Block3.entries 19 19 := by
  decide +kernel

theorem entry_reindex_19_20 :
    Integer.Sparse.reindex key entry_19_20 = GramEntries.Block3.entries 19 20 := by
  decide +kernel

theorem entry_reindex_19_21 :
    Integer.Sparse.reindex key entry_19_21 = GramEntries.Block3.entries 19 21 := by
  decide +kernel

theorem entry_reindex_19_22 :
    Integer.Sparse.reindex key entry_19_22 = GramEntries.Block3.entries 19 22 := by
  decide +kernel

theorem entry_reindex_19_23 :
    Integer.Sparse.reindex key entry_19_23 = GramEntries.Block3.entries 19 23 := by
  decide +kernel

theorem entry_reindex_19_24 :
    Integer.Sparse.reindex key entry_19_24 = GramEntries.Block3.entries 19 24 := by
  decide +kernel

theorem entry_reindex_19_25 :
    Integer.Sparse.reindex key entry_19_25 = GramEntries.Block3.entries 19 25 := by
  decide +kernel

theorem entry_reindex_19_26 :
    Integer.Sparse.reindex key entry_19_26 = GramEntries.Block3.entries 19 26 := by
  decide +kernel

theorem entries_reindex_19 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 19 j) = GramEntries.Block3.entries 19 j := by
  fin_cases j
  · exact entry_reindex_19_0
  · exact entry_reindex_19_1
  · exact entry_reindex_19_2
  · exact entry_reindex_19_3
  · exact entry_reindex_19_4
  · exact entry_reindex_19_5
  · exact entry_reindex_19_6
  · exact entry_reindex_19_7
  · exact entry_reindex_19_8
  · exact entry_reindex_19_9
  · exact entry_reindex_19_10
  · exact entry_reindex_19_11
  · exact entry_reindex_19_12
  · exact entry_reindex_19_13
  · exact entry_reindex_19_14
  · exact entry_reindex_19_15
  · exact entry_reindex_19_16
  · exact entry_reindex_19_17
  · exact entry_reindex_19_18
  · exact entry_reindex_19_19
  · exact entry_reindex_19_20
  · exact entry_reindex_19_21
  · exact entry_reindex_19_22
  · exact entry_reindex_19_23
  · exact entry_reindex_19_24
  · exact entry_reindex_19_25
  · exact entry_reindex_19_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_2_0 :
    Integer.Sparse.reindex key entry_2_0 = GramEntries.Block3.entries 2 0 := by
  decide +kernel

theorem entry_reindex_2_1 :
    Integer.Sparse.reindex key entry_2_1 = GramEntries.Block3.entries 2 1 := by
  decide +kernel

theorem entry_reindex_2_2 :
    Integer.Sparse.reindex key entry_2_2 = GramEntries.Block3.entries 2 2 := by
  decide +kernel

theorem entry_reindex_2_3 :
    Integer.Sparse.reindex key entry_2_3 = GramEntries.Block3.entries 2 3 := by
  decide +kernel

theorem entry_reindex_2_4 :
    Integer.Sparse.reindex key entry_2_4 = GramEntries.Block3.entries 2 4 := by
  decide +kernel

theorem entry_reindex_2_5 :
    Integer.Sparse.reindex key entry_2_5 = GramEntries.Block3.entries 2 5 := by
  decide +kernel

theorem entry_reindex_2_6 :
    Integer.Sparse.reindex key entry_2_6 = GramEntries.Block3.entries 2 6 := by
  decide +kernel

theorem entry_reindex_2_7 :
    Integer.Sparse.reindex key entry_2_7 = GramEntries.Block3.entries 2 7 := by
  decide +kernel

theorem entry_reindex_2_8 :
    Integer.Sparse.reindex key entry_2_8 = GramEntries.Block3.entries 2 8 := by
  decide +kernel

theorem entry_reindex_2_9 :
    Integer.Sparse.reindex key entry_2_9 = GramEntries.Block3.entries 2 9 := by
  decide +kernel

theorem entry_reindex_2_10 :
    Integer.Sparse.reindex key entry_2_10 = GramEntries.Block3.entries 2 10 := by
  decide +kernel

theorem entry_reindex_2_11 :
    Integer.Sparse.reindex key entry_2_11 = GramEntries.Block3.entries 2 11 := by
  decide +kernel

theorem entry_reindex_2_12 :
    Integer.Sparse.reindex key entry_2_12 = GramEntries.Block3.entries 2 12 := by
  decide +kernel

theorem entry_reindex_2_13 :
    Integer.Sparse.reindex key entry_2_13 = GramEntries.Block3.entries 2 13 := by
  decide +kernel

theorem entry_reindex_2_14 :
    Integer.Sparse.reindex key entry_2_14 = GramEntries.Block3.entries 2 14 := by
  decide +kernel

theorem entry_reindex_2_15 :
    Integer.Sparse.reindex key entry_2_15 = GramEntries.Block3.entries 2 15 := by
  decide +kernel

theorem entry_reindex_2_16 :
    Integer.Sparse.reindex key entry_2_16 = GramEntries.Block3.entries 2 16 := by
  decide +kernel

theorem entry_reindex_2_17 :
    Integer.Sparse.reindex key entry_2_17 = GramEntries.Block3.entries 2 17 := by
  decide +kernel

theorem entry_reindex_2_18 :
    Integer.Sparse.reindex key entry_2_18 = GramEntries.Block3.entries 2 18 := by
  decide +kernel

theorem entry_reindex_2_19 :
    Integer.Sparse.reindex key entry_2_19 = GramEntries.Block3.entries 2 19 := by
  decide +kernel

theorem entry_reindex_2_20 :
    Integer.Sparse.reindex key entry_2_20 = GramEntries.Block3.entries 2 20 := by
  decide +kernel

theorem entry_reindex_2_21 :
    Integer.Sparse.reindex key entry_2_21 = GramEntries.Block3.entries 2 21 := by
  decide +kernel

theorem entry_reindex_2_22 :
    Integer.Sparse.reindex key entry_2_22 = GramEntries.Block3.entries 2 22 := by
  decide +kernel

theorem entry_reindex_2_23 :
    Integer.Sparse.reindex key entry_2_23 = GramEntries.Block3.entries 2 23 := by
  decide +kernel

theorem entry_reindex_2_24 :
    Integer.Sparse.reindex key entry_2_24 = GramEntries.Block3.entries 2 24 := by
  decide +kernel

theorem entry_reindex_2_25 :
    Integer.Sparse.reindex key entry_2_25 = GramEntries.Block3.entries 2 25 := by
  decide +kernel

theorem entry_reindex_2_26 :
    Integer.Sparse.reindex key entry_2_26 = GramEntries.Block3.entries 2 26 := by
  decide +kernel

theorem entries_reindex_2 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 2 j) = GramEntries.Block3.entries 2 j := by
  fin_cases j
  · exact entry_reindex_2_0
  · exact entry_reindex_2_1
  · exact entry_reindex_2_2
  · exact entry_reindex_2_3
  · exact entry_reindex_2_4
  · exact entry_reindex_2_5
  · exact entry_reindex_2_6
  · exact entry_reindex_2_7
  · exact entry_reindex_2_8
  · exact entry_reindex_2_9
  · exact entry_reindex_2_10
  · exact entry_reindex_2_11
  · exact entry_reindex_2_12
  · exact entry_reindex_2_13
  · exact entry_reindex_2_14
  · exact entry_reindex_2_15
  · exact entry_reindex_2_16
  · exact entry_reindex_2_17
  · exact entry_reindex_2_18
  · exact entry_reindex_2_19
  · exact entry_reindex_2_20
  · exact entry_reindex_2_21
  · exact entry_reindex_2_22
  · exact entry_reindex_2_23
  · exact entry_reindex_2_24
  · exact entry_reindex_2_25
  · exact entry_reindex_2_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex20
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_20_0 :
    Integer.Sparse.reindex key entry_20_0 = GramEntries.Block3.entries 20 0 := by
  decide +kernel

theorem entry_reindex_20_1 :
    Integer.Sparse.reindex key entry_20_1 = GramEntries.Block3.entries 20 1 := by
  decide +kernel

theorem entry_reindex_20_2 :
    Integer.Sparse.reindex key entry_20_2 = GramEntries.Block3.entries 20 2 := by
  decide +kernel

theorem entry_reindex_20_3 :
    Integer.Sparse.reindex key entry_20_3 = GramEntries.Block3.entries 20 3 := by
  decide +kernel

theorem entry_reindex_20_4 :
    Integer.Sparse.reindex key entry_20_4 = GramEntries.Block3.entries 20 4 := by
  decide +kernel

theorem entry_reindex_20_5 :
    Integer.Sparse.reindex key entry_20_5 = GramEntries.Block3.entries 20 5 := by
  decide +kernel

theorem entry_reindex_20_6 :
    Integer.Sparse.reindex key entry_20_6 = GramEntries.Block3.entries 20 6 := by
  decide +kernel

theorem entry_reindex_20_7 :
    Integer.Sparse.reindex key entry_20_7 = GramEntries.Block3.entries 20 7 := by
  decide +kernel

theorem entry_reindex_20_8 :
    Integer.Sparse.reindex key entry_20_8 = GramEntries.Block3.entries 20 8 := by
  decide +kernel

theorem entry_reindex_20_9 :
    Integer.Sparse.reindex key entry_20_9 = GramEntries.Block3.entries 20 9 := by
  decide +kernel

theorem entry_reindex_20_10 :
    Integer.Sparse.reindex key entry_20_10 = GramEntries.Block3.entries 20 10 := by
  decide +kernel

theorem entry_reindex_20_11 :
    Integer.Sparse.reindex key entry_20_11 = GramEntries.Block3.entries 20 11 := by
  decide +kernel

theorem entry_reindex_20_12 :
    Integer.Sparse.reindex key entry_20_12 = GramEntries.Block3.entries 20 12 := by
  decide +kernel

theorem entry_reindex_20_13 :
    Integer.Sparse.reindex key entry_20_13 = GramEntries.Block3.entries 20 13 := by
  decide +kernel

theorem entry_reindex_20_14 :
    Integer.Sparse.reindex key entry_20_14 = GramEntries.Block3.entries 20 14 := by
  decide +kernel

theorem entry_reindex_20_15 :
    Integer.Sparse.reindex key entry_20_15 = GramEntries.Block3.entries 20 15 := by
  decide +kernel

theorem entry_reindex_20_16 :
    Integer.Sparse.reindex key entry_20_16 = GramEntries.Block3.entries 20 16 := by
  decide +kernel

theorem entry_reindex_20_17 :
    Integer.Sparse.reindex key entry_20_17 = GramEntries.Block3.entries 20 17 := by
  decide +kernel

theorem entry_reindex_20_18 :
    Integer.Sparse.reindex key entry_20_18 = GramEntries.Block3.entries 20 18 := by
  decide +kernel

theorem entry_reindex_20_19 :
    Integer.Sparse.reindex key entry_20_19 = GramEntries.Block3.entries 20 19 := by
  decide +kernel

theorem entry_reindex_20_20 :
    Integer.Sparse.reindex key entry_20_20 = GramEntries.Block3.entries 20 20 := by
  decide +kernel

theorem entry_reindex_20_21 :
    Integer.Sparse.reindex key entry_20_21 = GramEntries.Block3.entries 20 21 := by
  decide +kernel

theorem entry_reindex_20_22 :
    Integer.Sparse.reindex key entry_20_22 = GramEntries.Block3.entries 20 22 := by
  decide +kernel

theorem entry_reindex_20_23 :
    Integer.Sparse.reindex key entry_20_23 = GramEntries.Block3.entries 20 23 := by
  decide +kernel

theorem entry_reindex_20_24 :
    Integer.Sparse.reindex key entry_20_24 = GramEntries.Block3.entries 20 24 := by
  decide +kernel

theorem entry_reindex_20_25 :
    Integer.Sparse.reindex key entry_20_25 = GramEntries.Block3.entries 20 25 := by
  decide +kernel

theorem entry_reindex_20_26 :
    Integer.Sparse.reindex key entry_20_26 = GramEntries.Block3.entries 20 26 := by
  decide +kernel

theorem entries_reindex_20 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 20 j) = GramEntries.Block3.entries 20 j := by
  fin_cases j
  · exact entry_reindex_20_0
  · exact entry_reindex_20_1
  · exact entry_reindex_20_2
  · exact entry_reindex_20_3
  · exact entry_reindex_20_4
  · exact entry_reindex_20_5
  · exact entry_reindex_20_6
  · exact entry_reindex_20_7
  · exact entry_reindex_20_8
  · exact entry_reindex_20_9
  · exact entry_reindex_20_10
  · exact entry_reindex_20_11
  · exact entry_reindex_20_12
  · exact entry_reindex_20_13
  · exact entry_reindex_20_14
  · exact entry_reindex_20_15
  · exact entry_reindex_20_16
  · exact entry_reindex_20_17
  · exact entry_reindex_20_18
  · exact entry_reindex_20_19
  · exact entry_reindex_20_20
  · exact entry_reindex_20_21
  · exact entry_reindex_20_22
  · exact entry_reindex_20_23
  · exact entry_reindex_20_24
  · exact entry_reindex_20_25
  · exact entry_reindex_20_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex21
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_21_0 :
    Integer.Sparse.reindex key entry_21_0 = GramEntries.Block3.entries 21 0 := by
  decide +kernel

theorem entry_reindex_21_1 :
    Integer.Sparse.reindex key entry_21_1 = GramEntries.Block3.entries 21 1 := by
  decide +kernel

theorem entry_reindex_21_2 :
    Integer.Sparse.reindex key entry_21_2 = GramEntries.Block3.entries 21 2 := by
  decide +kernel

theorem entry_reindex_21_3 :
    Integer.Sparse.reindex key entry_21_3 = GramEntries.Block3.entries 21 3 := by
  decide +kernel

theorem entry_reindex_21_4 :
    Integer.Sparse.reindex key entry_21_4 = GramEntries.Block3.entries 21 4 := by
  decide +kernel

theorem entry_reindex_21_5 :
    Integer.Sparse.reindex key entry_21_5 = GramEntries.Block3.entries 21 5 := by
  decide +kernel

theorem entry_reindex_21_6 :
    Integer.Sparse.reindex key entry_21_6 = GramEntries.Block3.entries 21 6 := by
  decide +kernel

theorem entry_reindex_21_7 :
    Integer.Sparse.reindex key entry_21_7 = GramEntries.Block3.entries 21 7 := by
  decide +kernel

theorem entry_reindex_21_8 :
    Integer.Sparse.reindex key entry_21_8 = GramEntries.Block3.entries 21 8 := by
  decide +kernel

theorem entry_reindex_21_9 :
    Integer.Sparse.reindex key entry_21_9 = GramEntries.Block3.entries 21 9 := by
  decide +kernel

theorem entry_reindex_21_10 :
    Integer.Sparse.reindex key entry_21_10 = GramEntries.Block3.entries 21 10 := by
  decide +kernel

theorem entry_reindex_21_11 :
    Integer.Sparse.reindex key entry_21_11 = GramEntries.Block3.entries 21 11 := by
  decide +kernel

theorem entry_reindex_21_12 :
    Integer.Sparse.reindex key entry_21_12 = GramEntries.Block3.entries 21 12 := by
  decide +kernel

theorem entry_reindex_21_13 :
    Integer.Sparse.reindex key entry_21_13 = GramEntries.Block3.entries 21 13 := by
  decide +kernel

theorem entry_reindex_21_14 :
    Integer.Sparse.reindex key entry_21_14 = GramEntries.Block3.entries 21 14 := by
  decide +kernel

theorem entry_reindex_21_15 :
    Integer.Sparse.reindex key entry_21_15 = GramEntries.Block3.entries 21 15 := by
  decide +kernel

theorem entry_reindex_21_16 :
    Integer.Sparse.reindex key entry_21_16 = GramEntries.Block3.entries 21 16 := by
  decide +kernel

theorem entry_reindex_21_17 :
    Integer.Sparse.reindex key entry_21_17 = GramEntries.Block3.entries 21 17 := by
  decide +kernel

theorem entry_reindex_21_18 :
    Integer.Sparse.reindex key entry_21_18 = GramEntries.Block3.entries 21 18 := by
  decide +kernel

theorem entry_reindex_21_19 :
    Integer.Sparse.reindex key entry_21_19 = GramEntries.Block3.entries 21 19 := by
  decide +kernel

theorem entry_reindex_21_20 :
    Integer.Sparse.reindex key entry_21_20 = GramEntries.Block3.entries 21 20 := by
  decide +kernel

theorem entry_reindex_21_21 :
    Integer.Sparse.reindex key entry_21_21 = GramEntries.Block3.entries 21 21 := by
  decide +kernel

theorem entry_reindex_21_22 :
    Integer.Sparse.reindex key entry_21_22 = GramEntries.Block3.entries 21 22 := by
  decide +kernel

theorem entry_reindex_21_23 :
    Integer.Sparse.reindex key entry_21_23 = GramEntries.Block3.entries 21 23 := by
  decide +kernel

theorem entry_reindex_21_24 :
    Integer.Sparse.reindex key entry_21_24 = GramEntries.Block3.entries 21 24 := by
  decide +kernel

theorem entry_reindex_21_25 :
    Integer.Sparse.reindex key entry_21_25 = GramEntries.Block3.entries 21 25 := by
  decide +kernel

theorem entry_reindex_21_26 :
    Integer.Sparse.reindex key entry_21_26 = GramEntries.Block3.entries 21 26 := by
  decide +kernel

theorem entries_reindex_21 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 21 j) = GramEntries.Block3.entries 21 j := by
  fin_cases j
  · exact entry_reindex_21_0
  · exact entry_reindex_21_1
  · exact entry_reindex_21_2
  · exact entry_reindex_21_3
  · exact entry_reindex_21_4
  · exact entry_reindex_21_5
  · exact entry_reindex_21_6
  · exact entry_reindex_21_7
  · exact entry_reindex_21_8
  · exact entry_reindex_21_9
  · exact entry_reindex_21_10
  · exact entry_reindex_21_11
  · exact entry_reindex_21_12
  · exact entry_reindex_21_13
  · exact entry_reindex_21_14
  · exact entry_reindex_21_15
  · exact entry_reindex_21_16
  · exact entry_reindex_21_17
  · exact entry_reindex_21_18
  · exact entry_reindex_21_19
  · exact entry_reindex_21_20
  · exact entry_reindex_21_21
  · exact entry_reindex_21_22
  · exact entry_reindex_21_23
  · exact entry_reindex_21_24
  · exact entry_reindex_21_25
  · exact entry_reindex_21_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_22_0 :
    Integer.Sparse.reindex key entry_22_0 = GramEntries.Block3.entries 22 0 := by
  decide +kernel

theorem entry_reindex_22_1 :
    Integer.Sparse.reindex key entry_22_1 = GramEntries.Block3.entries 22 1 := by
  decide +kernel

theorem entry_reindex_22_2 :
    Integer.Sparse.reindex key entry_22_2 = GramEntries.Block3.entries 22 2 := by
  decide +kernel

theorem entry_reindex_22_3 :
    Integer.Sparse.reindex key entry_22_3 = GramEntries.Block3.entries 22 3 := by
  decide +kernel

theorem entry_reindex_22_4 :
    Integer.Sparse.reindex key entry_22_4 = GramEntries.Block3.entries 22 4 := by
  decide +kernel

theorem entry_reindex_22_5 :
    Integer.Sparse.reindex key entry_22_5 = GramEntries.Block3.entries 22 5 := by
  decide +kernel

theorem entry_reindex_22_6 :
    Integer.Sparse.reindex key entry_22_6 = GramEntries.Block3.entries 22 6 := by
  decide +kernel

theorem entry_reindex_22_7 :
    Integer.Sparse.reindex key entry_22_7 = GramEntries.Block3.entries 22 7 := by
  decide +kernel

theorem entry_reindex_22_8 :
    Integer.Sparse.reindex key entry_22_8 = GramEntries.Block3.entries 22 8 := by
  decide +kernel

theorem entry_reindex_22_9 :
    Integer.Sparse.reindex key entry_22_9 = GramEntries.Block3.entries 22 9 := by
  decide +kernel

theorem entry_reindex_22_10 :
    Integer.Sparse.reindex key entry_22_10 = GramEntries.Block3.entries 22 10 := by
  decide +kernel

theorem entry_reindex_22_11 :
    Integer.Sparse.reindex key entry_22_11 = GramEntries.Block3.entries 22 11 := by
  decide +kernel

theorem entry_reindex_22_12 :
    Integer.Sparse.reindex key entry_22_12 = GramEntries.Block3.entries 22 12 := by
  decide +kernel

theorem entry_reindex_22_13 :
    Integer.Sparse.reindex key entry_22_13 = GramEntries.Block3.entries 22 13 := by
  decide +kernel

theorem entry_reindex_22_14 :
    Integer.Sparse.reindex key entry_22_14 = GramEntries.Block3.entries 22 14 := by
  decide +kernel

theorem entry_reindex_22_15 :
    Integer.Sparse.reindex key entry_22_15 = GramEntries.Block3.entries 22 15 := by
  decide +kernel

theorem entry_reindex_22_16 :
    Integer.Sparse.reindex key entry_22_16 = GramEntries.Block3.entries 22 16 := by
  decide +kernel

theorem entry_reindex_22_17 :
    Integer.Sparse.reindex key entry_22_17 = GramEntries.Block3.entries 22 17 := by
  decide +kernel

theorem entry_reindex_22_18 :
    Integer.Sparse.reindex key entry_22_18 = GramEntries.Block3.entries 22 18 := by
  decide +kernel

theorem entry_reindex_22_19 :
    Integer.Sparse.reindex key entry_22_19 = GramEntries.Block3.entries 22 19 := by
  decide +kernel

theorem entry_reindex_22_20 :
    Integer.Sparse.reindex key entry_22_20 = GramEntries.Block3.entries 22 20 := by
  decide +kernel

theorem entry_reindex_22_21 :
    Integer.Sparse.reindex key entry_22_21 = GramEntries.Block3.entries 22 21 := by
  decide +kernel

theorem entry_reindex_22_22 :
    Integer.Sparse.reindex key entry_22_22 = GramEntries.Block3.entries 22 22 := by
  decide +kernel

theorem entry_reindex_22_23 :
    Integer.Sparse.reindex key entry_22_23 = GramEntries.Block3.entries 22 23 := by
  decide +kernel

theorem entry_reindex_22_24 :
    Integer.Sparse.reindex key entry_22_24 = GramEntries.Block3.entries 22 24 := by
  decide +kernel

theorem entry_reindex_22_25 :
    Integer.Sparse.reindex key entry_22_25 = GramEntries.Block3.entries 22 25 := by
  decide +kernel

theorem entry_reindex_22_26 :
    Integer.Sparse.reindex key entry_22_26 = GramEntries.Block3.entries 22 26 := by
  decide +kernel

theorem entries_reindex_22 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 22 j) = GramEntries.Block3.entries 22 j := by
  fin_cases j
  · exact entry_reindex_22_0
  · exact entry_reindex_22_1
  · exact entry_reindex_22_2
  · exact entry_reindex_22_3
  · exact entry_reindex_22_4
  · exact entry_reindex_22_5
  · exact entry_reindex_22_6
  · exact entry_reindex_22_7
  · exact entry_reindex_22_8
  · exact entry_reindex_22_9
  · exact entry_reindex_22_10
  · exact entry_reindex_22_11
  · exact entry_reindex_22_12
  · exact entry_reindex_22_13
  · exact entry_reindex_22_14
  · exact entry_reindex_22_15
  · exact entry_reindex_22_16
  · exact entry_reindex_22_17
  · exact entry_reindex_22_18
  · exact entry_reindex_22_19
  · exact entry_reindex_22_20
  · exact entry_reindex_22_21
  · exact entry_reindex_22_22
  · exact entry_reindex_22_23
  · exact entry_reindex_22_24
  · exact entry_reindex_22_25
  · exact entry_reindex_22_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_23_0 :
    Integer.Sparse.reindex key entry_23_0 = GramEntries.Block3.entries 23 0 := by
  decide +kernel

theorem entry_reindex_23_1 :
    Integer.Sparse.reindex key entry_23_1 = GramEntries.Block3.entries 23 1 := by
  decide +kernel

theorem entry_reindex_23_2 :
    Integer.Sparse.reindex key entry_23_2 = GramEntries.Block3.entries 23 2 := by
  decide +kernel

theorem entry_reindex_23_3 :
    Integer.Sparse.reindex key entry_23_3 = GramEntries.Block3.entries 23 3 := by
  decide +kernel

theorem entry_reindex_23_4 :
    Integer.Sparse.reindex key entry_23_4 = GramEntries.Block3.entries 23 4 := by
  decide +kernel

theorem entry_reindex_23_5 :
    Integer.Sparse.reindex key entry_23_5 = GramEntries.Block3.entries 23 5 := by
  decide +kernel

theorem entry_reindex_23_6 :
    Integer.Sparse.reindex key entry_23_6 = GramEntries.Block3.entries 23 6 := by
  decide +kernel

theorem entry_reindex_23_7 :
    Integer.Sparse.reindex key entry_23_7 = GramEntries.Block3.entries 23 7 := by
  decide +kernel

theorem entry_reindex_23_8 :
    Integer.Sparse.reindex key entry_23_8 = GramEntries.Block3.entries 23 8 := by
  decide +kernel

theorem entry_reindex_23_9 :
    Integer.Sparse.reindex key entry_23_9 = GramEntries.Block3.entries 23 9 := by
  decide +kernel

theorem entry_reindex_23_10 :
    Integer.Sparse.reindex key entry_23_10 = GramEntries.Block3.entries 23 10 := by
  decide +kernel

theorem entry_reindex_23_11 :
    Integer.Sparse.reindex key entry_23_11 = GramEntries.Block3.entries 23 11 := by
  decide +kernel

theorem entry_reindex_23_12 :
    Integer.Sparse.reindex key entry_23_12 = GramEntries.Block3.entries 23 12 := by
  decide +kernel

theorem entry_reindex_23_13 :
    Integer.Sparse.reindex key entry_23_13 = GramEntries.Block3.entries 23 13 := by
  decide +kernel

theorem entry_reindex_23_14 :
    Integer.Sparse.reindex key entry_23_14 = GramEntries.Block3.entries 23 14 := by
  decide +kernel

theorem entry_reindex_23_15 :
    Integer.Sparse.reindex key entry_23_15 = GramEntries.Block3.entries 23 15 := by
  decide +kernel

theorem entry_reindex_23_16 :
    Integer.Sparse.reindex key entry_23_16 = GramEntries.Block3.entries 23 16 := by
  decide +kernel

theorem entry_reindex_23_17 :
    Integer.Sparse.reindex key entry_23_17 = GramEntries.Block3.entries 23 17 := by
  decide +kernel

theorem entry_reindex_23_18 :
    Integer.Sparse.reindex key entry_23_18 = GramEntries.Block3.entries 23 18 := by
  decide +kernel

theorem entry_reindex_23_19 :
    Integer.Sparse.reindex key entry_23_19 = GramEntries.Block3.entries 23 19 := by
  decide +kernel

theorem entry_reindex_23_20 :
    Integer.Sparse.reindex key entry_23_20 = GramEntries.Block3.entries 23 20 := by
  decide +kernel

theorem entry_reindex_23_21 :
    Integer.Sparse.reindex key entry_23_21 = GramEntries.Block3.entries 23 21 := by
  decide +kernel

theorem entry_reindex_23_22 :
    Integer.Sparse.reindex key entry_23_22 = GramEntries.Block3.entries 23 22 := by
  decide +kernel

theorem entry_reindex_23_23 :
    Integer.Sparse.reindex key entry_23_23 = GramEntries.Block3.entries 23 23 := by
  decide +kernel

theorem entry_reindex_23_24 :
    Integer.Sparse.reindex key entry_23_24 = GramEntries.Block3.entries 23 24 := by
  decide +kernel

theorem entry_reindex_23_25 :
    Integer.Sparse.reindex key entry_23_25 = GramEntries.Block3.entries 23 25 := by
  decide +kernel

theorem entry_reindex_23_26 :
    Integer.Sparse.reindex key entry_23_26 = GramEntries.Block3.entries 23 26 := by
  decide +kernel

theorem entries_reindex_23 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 23 j) = GramEntries.Block3.entries 23 j := by
  fin_cases j
  · exact entry_reindex_23_0
  · exact entry_reindex_23_1
  · exact entry_reindex_23_2
  · exact entry_reindex_23_3
  · exact entry_reindex_23_4
  · exact entry_reindex_23_5
  · exact entry_reindex_23_6
  · exact entry_reindex_23_7
  · exact entry_reindex_23_8
  · exact entry_reindex_23_9
  · exact entry_reindex_23_10
  · exact entry_reindex_23_11
  · exact entry_reindex_23_12
  · exact entry_reindex_23_13
  · exact entry_reindex_23_14
  · exact entry_reindex_23_15
  · exact entry_reindex_23_16
  · exact entry_reindex_23_17
  · exact entry_reindex_23_18
  · exact entry_reindex_23_19
  · exact entry_reindex_23_20
  · exact entry_reindex_23_21
  · exact entry_reindex_23_22
  · exact entry_reindex_23_23
  · exact entry_reindex_23_24
  · exact entry_reindex_23_25
  · exact entry_reindex_23_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex24
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_24_0 :
    Integer.Sparse.reindex key entry_24_0 = GramEntries.Block3.entries 24 0 := by
  decide +kernel

theorem entry_reindex_24_1 :
    Integer.Sparse.reindex key entry_24_1 = GramEntries.Block3.entries 24 1 := by
  decide +kernel

theorem entry_reindex_24_2 :
    Integer.Sparse.reindex key entry_24_2 = GramEntries.Block3.entries 24 2 := by
  decide +kernel

theorem entry_reindex_24_3 :
    Integer.Sparse.reindex key entry_24_3 = GramEntries.Block3.entries 24 3 := by
  decide +kernel

theorem entry_reindex_24_4 :
    Integer.Sparse.reindex key entry_24_4 = GramEntries.Block3.entries 24 4 := by
  decide +kernel

theorem entry_reindex_24_5 :
    Integer.Sparse.reindex key entry_24_5 = GramEntries.Block3.entries 24 5 := by
  decide +kernel

theorem entry_reindex_24_6 :
    Integer.Sparse.reindex key entry_24_6 = GramEntries.Block3.entries 24 6 := by
  decide +kernel

theorem entry_reindex_24_7 :
    Integer.Sparse.reindex key entry_24_7 = GramEntries.Block3.entries 24 7 := by
  decide +kernel

theorem entry_reindex_24_8 :
    Integer.Sparse.reindex key entry_24_8 = GramEntries.Block3.entries 24 8 := by
  decide +kernel

theorem entry_reindex_24_9 :
    Integer.Sparse.reindex key entry_24_9 = GramEntries.Block3.entries 24 9 := by
  decide +kernel

theorem entry_reindex_24_10 :
    Integer.Sparse.reindex key entry_24_10 = GramEntries.Block3.entries 24 10 := by
  decide +kernel

theorem entry_reindex_24_11 :
    Integer.Sparse.reindex key entry_24_11 = GramEntries.Block3.entries 24 11 := by
  decide +kernel

theorem entry_reindex_24_12 :
    Integer.Sparse.reindex key entry_24_12 = GramEntries.Block3.entries 24 12 := by
  decide +kernel

theorem entry_reindex_24_13 :
    Integer.Sparse.reindex key entry_24_13 = GramEntries.Block3.entries 24 13 := by
  decide +kernel

theorem entry_reindex_24_14 :
    Integer.Sparse.reindex key entry_24_14 = GramEntries.Block3.entries 24 14 := by
  decide +kernel

theorem entry_reindex_24_15 :
    Integer.Sparse.reindex key entry_24_15 = GramEntries.Block3.entries 24 15 := by
  decide +kernel

theorem entry_reindex_24_16 :
    Integer.Sparse.reindex key entry_24_16 = GramEntries.Block3.entries 24 16 := by
  decide +kernel

theorem entry_reindex_24_17 :
    Integer.Sparse.reindex key entry_24_17 = GramEntries.Block3.entries 24 17 := by
  decide +kernel

theorem entry_reindex_24_18 :
    Integer.Sparse.reindex key entry_24_18 = GramEntries.Block3.entries 24 18 := by
  decide +kernel

theorem entry_reindex_24_19 :
    Integer.Sparse.reindex key entry_24_19 = GramEntries.Block3.entries 24 19 := by
  decide +kernel

theorem entry_reindex_24_20 :
    Integer.Sparse.reindex key entry_24_20 = GramEntries.Block3.entries 24 20 := by
  decide +kernel

theorem entry_reindex_24_21 :
    Integer.Sparse.reindex key entry_24_21 = GramEntries.Block3.entries 24 21 := by
  decide +kernel

theorem entry_reindex_24_22 :
    Integer.Sparse.reindex key entry_24_22 = GramEntries.Block3.entries 24 22 := by
  decide +kernel

theorem entry_reindex_24_23 :
    Integer.Sparse.reindex key entry_24_23 = GramEntries.Block3.entries 24 23 := by
  decide +kernel

theorem entry_reindex_24_24 :
    Integer.Sparse.reindex key entry_24_24 = GramEntries.Block3.entries 24 24 := by
  decide +kernel

theorem entry_reindex_24_25 :
    Integer.Sparse.reindex key entry_24_25 = GramEntries.Block3.entries 24 25 := by
  decide +kernel

theorem entry_reindex_24_26 :
    Integer.Sparse.reindex key entry_24_26 = GramEntries.Block3.entries 24 26 := by
  decide +kernel

theorem entries_reindex_24 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 24 j) = GramEntries.Block3.entries 24 j := by
  fin_cases j
  · exact entry_reindex_24_0
  · exact entry_reindex_24_1
  · exact entry_reindex_24_2
  · exact entry_reindex_24_3
  · exact entry_reindex_24_4
  · exact entry_reindex_24_5
  · exact entry_reindex_24_6
  · exact entry_reindex_24_7
  · exact entry_reindex_24_8
  · exact entry_reindex_24_9
  · exact entry_reindex_24_10
  · exact entry_reindex_24_11
  · exact entry_reindex_24_12
  · exact entry_reindex_24_13
  · exact entry_reindex_24_14
  · exact entry_reindex_24_15
  · exact entry_reindex_24_16
  · exact entry_reindex_24_17
  · exact entry_reindex_24_18
  · exact entry_reindex_24_19
  · exact entry_reindex_24_20
  · exact entry_reindex_24_21
  · exact entry_reindex_24_22
  · exact entry_reindex_24_23
  · exact entry_reindex_24_24
  · exact entry_reindex_24_25
  · exact entry_reindex_24_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex25
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_25_0 :
    Integer.Sparse.reindex key entry_25_0 = GramEntries.Block3.entries 25 0 := by
  decide +kernel

theorem entry_reindex_25_1 :
    Integer.Sparse.reindex key entry_25_1 = GramEntries.Block3.entries 25 1 := by
  decide +kernel

theorem entry_reindex_25_2 :
    Integer.Sparse.reindex key entry_25_2 = GramEntries.Block3.entries 25 2 := by
  decide +kernel

theorem entry_reindex_25_3 :
    Integer.Sparse.reindex key entry_25_3 = GramEntries.Block3.entries 25 3 := by
  decide +kernel

theorem entry_reindex_25_4 :
    Integer.Sparse.reindex key entry_25_4 = GramEntries.Block3.entries 25 4 := by
  decide +kernel

theorem entry_reindex_25_5 :
    Integer.Sparse.reindex key entry_25_5 = GramEntries.Block3.entries 25 5 := by
  decide +kernel

theorem entry_reindex_25_6 :
    Integer.Sparse.reindex key entry_25_6 = GramEntries.Block3.entries 25 6 := by
  decide +kernel

theorem entry_reindex_25_7 :
    Integer.Sparse.reindex key entry_25_7 = GramEntries.Block3.entries 25 7 := by
  decide +kernel

theorem entry_reindex_25_8 :
    Integer.Sparse.reindex key entry_25_8 = GramEntries.Block3.entries 25 8 := by
  decide +kernel

theorem entry_reindex_25_9 :
    Integer.Sparse.reindex key entry_25_9 = GramEntries.Block3.entries 25 9 := by
  decide +kernel

theorem entry_reindex_25_10 :
    Integer.Sparse.reindex key entry_25_10 = GramEntries.Block3.entries 25 10 := by
  decide +kernel

theorem entry_reindex_25_11 :
    Integer.Sparse.reindex key entry_25_11 = GramEntries.Block3.entries 25 11 := by
  decide +kernel

theorem entry_reindex_25_12 :
    Integer.Sparse.reindex key entry_25_12 = GramEntries.Block3.entries 25 12 := by
  decide +kernel

theorem entry_reindex_25_13 :
    Integer.Sparse.reindex key entry_25_13 = GramEntries.Block3.entries 25 13 := by
  decide +kernel

theorem entry_reindex_25_14 :
    Integer.Sparse.reindex key entry_25_14 = GramEntries.Block3.entries 25 14 := by
  decide +kernel

theorem entry_reindex_25_15 :
    Integer.Sparse.reindex key entry_25_15 = GramEntries.Block3.entries 25 15 := by
  decide +kernel

theorem entry_reindex_25_16 :
    Integer.Sparse.reindex key entry_25_16 = GramEntries.Block3.entries 25 16 := by
  decide +kernel

theorem entry_reindex_25_17 :
    Integer.Sparse.reindex key entry_25_17 = GramEntries.Block3.entries 25 17 := by
  decide +kernel

theorem entry_reindex_25_18 :
    Integer.Sparse.reindex key entry_25_18 = GramEntries.Block3.entries 25 18 := by
  decide +kernel

theorem entry_reindex_25_19 :
    Integer.Sparse.reindex key entry_25_19 = GramEntries.Block3.entries 25 19 := by
  decide +kernel

theorem entry_reindex_25_20 :
    Integer.Sparse.reindex key entry_25_20 = GramEntries.Block3.entries 25 20 := by
  decide +kernel

theorem entry_reindex_25_21 :
    Integer.Sparse.reindex key entry_25_21 = GramEntries.Block3.entries 25 21 := by
  decide +kernel

theorem entry_reindex_25_22 :
    Integer.Sparse.reindex key entry_25_22 = GramEntries.Block3.entries 25 22 := by
  decide +kernel

theorem entry_reindex_25_23 :
    Integer.Sparse.reindex key entry_25_23 = GramEntries.Block3.entries 25 23 := by
  decide +kernel

theorem entry_reindex_25_24 :
    Integer.Sparse.reindex key entry_25_24 = GramEntries.Block3.entries 25 24 := by
  decide +kernel

theorem entry_reindex_25_25 :
    Integer.Sparse.reindex key entry_25_25 = GramEntries.Block3.entries 25 25 := by
  decide +kernel

theorem entry_reindex_25_26 :
    Integer.Sparse.reindex key entry_25_26 = GramEntries.Block3.entries 25 26 := by
  decide +kernel

theorem entries_reindex_25 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 25 j) = GramEntries.Block3.entries 25 j := by
  fin_cases j
  · exact entry_reindex_25_0
  · exact entry_reindex_25_1
  · exact entry_reindex_25_2
  · exact entry_reindex_25_3
  · exact entry_reindex_25_4
  · exact entry_reindex_25_5
  · exact entry_reindex_25_6
  · exact entry_reindex_25_7
  · exact entry_reindex_25_8
  · exact entry_reindex_25_9
  · exact entry_reindex_25_10
  · exact entry_reindex_25_11
  · exact entry_reindex_25_12
  · exact entry_reindex_25_13
  · exact entry_reindex_25_14
  · exact entry_reindex_25_15
  · exact entry_reindex_25_16
  · exact entry_reindex_25_17
  · exact entry_reindex_25_18
  · exact entry_reindex_25_19
  · exact entry_reindex_25_20
  · exact entry_reindex_25_21
  · exact entry_reindex_25_22
  · exact entry_reindex_25_23
  · exact entry_reindex_25_24
  · exact entry_reindex_25_25
  · exact entry_reindex_25_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex26
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_26_0 :
    Integer.Sparse.reindex key entry_26_0 = GramEntries.Block3.entries 26 0 := by
  decide +kernel

theorem entry_reindex_26_1 :
    Integer.Sparse.reindex key entry_26_1 = GramEntries.Block3.entries 26 1 := by
  decide +kernel

theorem entry_reindex_26_2 :
    Integer.Sparse.reindex key entry_26_2 = GramEntries.Block3.entries 26 2 := by
  decide +kernel

theorem entry_reindex_26_3 :
    Integer.Sparse.reindex key entry_26_3 = GramEntries.Block3.entries 26 3 := by
  decide +kernel

theorem entry_reindex_26_4 :
    Integer.Sparse.reindex key entry_26_4 = GramEntries.Block3.entries 26 4 := by
  decide +kernel

theorem entry_reindex_26_5 :
    Integer.Sparse.reindex key entry_26_5 = GramEntries.Block3.entries 26 5 := by
  decide +kernel

theorem entry_reindex_26_6 :
    Integer.Sparse.reindex key entry_26_6 = GramEntries.Block3.entries 26 6 := by
  decide +kernel

theorem entry_reindex_26_7 :
    Integer.Sparse.reindex key entry_26_7 = GramEntries.Block3.entries 26 7 := by
  decide +kernel

theorem entry_reindex_26_8 :
    Integer.Sparse.reindex key entry_26_8 = GramEntries.Block3.entries 26 8 := by
  decide +kernel

theorem entry_reindex_26_9 :
    Integer.Sparse.reindex key entry_26_9 = GramEntries.Block3.entries 26 9 := by
  decide +kernel

theorem entry_reindex_26_10 :
    Integer.Sparse.reindex key entry_26_10 = GramEntries.Block3.entries 26 10 := by
  decide +kernel

theorem entry_reindex_26_11 :
    Integer.Sparse.reindex key entry_26_11 = GramEntries.Block3.entries 26 11 := by
  decide +kernel

theorem entry_reindex_26_12 :
    Integer.Sparse.reindex key entry_26_12 = GramEntries.Block3.entries 26 12 := by
  decide +kernel

theorem entry_reindex_26_13 :
    Integer.Sparse.reindex key entry_26_13 = GramEntries.Block3.entries 26 13 := by
  decide +kernel

theorem entry_reindex_26_14 :
    Integer.Sparse.reindex key entry_26_14 = GramEntries.Block3.entries 26 14 := by
  decide +kernel

theorem entry_reindex_26_15 :
    Integer.Sparse.reindex key entry_26_15 = GramEntries.Block3.entries 26 15 := by
  decide +kernel

theorem entry_reindex_26_16 :
    Integer.Sparse.reindex key entry_26_16 = GramEntries.Block3.entries 26 16 := by
  decide +kernel

theorem entry_reindex_26_17 :
    Integer.Sparse.reindex key entry_26_17 = GramEntries.Block3.entries 26 17 := by
  decide +kernel

theorem entry_reindex_26_18 :
    Integer.Sparse.reindex key entry_26_18 = GramEntries.Block3.entries 26 18 := by
  decide +kernel

theorem entry_reindex_26_19 :
    Integer.Sparse.reindex key entry_26_19 = GramEntries.Block3.entries 26 19 := by
  decide +kernel

theorem entry_reindex_26_20 :
    Integer.Sparse.reindex key entry_26_20 = GramEntries.Block3.entries 26 20 := by
  decide +kernel

theorem entry_reindex_26_21 :
    Integer.Sparse.reindex key entry_26_21 = GramEntries.Block3.entries 26 21 := by
  decide +kernel

theorem entry_reindex_26_22 :
    Integer.Sparse.reindex key entry_26_22 = GramEntries.Block3.entries 26 22 := by
  decide +kernel

theorem entry_reindex_26_23 :
    Integer.Sparse.reindex key entry_26_23 = GramEntries.Block3.entries 26 23 := by
  decide +kernel

theorem entry_reindex_26_24 :
    Integer.Sparse.reindex key entry_26_24 = GramEntries.Block3.entries 26 24 := by
  decide +kernel

theorem entry_reindex_26_25 :
    Integer.Sparse.reindex key entry_26_25 = GramEntries.Block3.entries 26 25 := by
  decide +kernel

theorem entry_reindex_26_26 :
    Integer.Sparse.reindex key entry_26_26 = GramEntries.Block3.entries 26 26 := by
  decide +kernel

theorem entries_reindex_26 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 26 j) = GramEntries.Block3.entries 26 j := by
  fin_cases j
  · exact entry_reindex_26_0
  · exact entry_reindex_26_1
  · exact entry_reindex_26_2
  · exact entry_reindex_26_3
  · exact entry_reindex_26_4
  · exact entry_reindex_26_5
  · exact entry_reindex_26_6
  · exact entry_reindex_26_7
  · exact entry_reindex_26_8
  · exact entry_reindex_26_9
  · exact entry_reindex_26_10
  · exact entry_reindex_26_11
  · exact entry_reindex_26_12
  · exact entry_reindex_26_13
  · exact entry_reindex_26_14
  · exact entry_reindex_26_15
  · exact entry_reindex_26_16
  · exact entry_reindex_26_17
  · exact entry_reindex_26_18
  · exact entry_reindex_26_19
  · exact entry_reindex_26_20
  · exact entry_reindex_26_21
  · exact entry_reindex_26_22
  · exact entry_reindex_26_23
  · exact entry_reindex_26_24
  · exact entry_reindex_26_25
  · exact entry_reindex_26_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex3
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_3_0 :
    Integer.Sparse.reindex key entry_3_0 = GramEntries.Block3.entries 3 0 := by
  decide +kernel

theorem entry_reindex_3_1 :
    Integer.Sparse.reindex key entry_3_1 = GramEntries.Block3.entries 3 1 := by
  decide +kernel

theorem entry_reindex_3_2 :
    Integer.Sparse.reindex key entry_3_2 = GramEntries.Block3.entries 3 2 := by
  decide +kernel

theorem entry_reindex_3_3 :
    Integer.Sparse.reindex key entry_3_3 = GramEntries.Block3.entries 3 3 := by
  decide +kernel

theorem entry_reindex_3_4 :
    Integer.Sparse.reindex key entry_3_4 = GramEntries.Block3.entries 3 4 := by
  decide +kernel

theorem entry_reindex_3_5 :
    Integer.Sparse.reindex key entry_3_5 = GramEntries.Block3.entries 3 5 := by
  decide +kernel

theorem entry_reindex_3_6 :
    Integer.Sparse.reindex key entry_3_6 = GramEntries.Block3.entries 3 6 := by
  decide +kernel

theorem entry_reindex_3_7 :
    Integer.Sparse.reindex key entry_3_7 = GramEntries.Block3.entries 3 7 := by
  decide +kernel

theorem entry_reindex_3_8 :
    Integer.Sparse.reindex key entry_3_8 = GramEntries.Block3.entries 3 8 := by
  decide +kernel

theorem entry_reindex_3_9 :
    Integer.Sparse.reindex key entry_3_9 = GramEntries.Block3.entries 3 9 := by
  decide +kernel

theorem entry_reindex_3_10 :
    Integer.Sparse.reindex key entry_3_10 = GramEntries.Block3.entries 3 10 := by
  decide +kernel

theorem entry_reindex_3_11 :
    Integer.Sparse.reindex key entry_3_11 = GramEntries.Block3.entries 3 11 := by
  decide +kernel

theorem entry_reindex_3_12 :
    Integer.Sparse.reindex key entry_3_12 = GramEntries.Block3.entries 3 12 := by
  decide +kernel

theorem entry_reindex_3_13 :
    Integer.Sparse.reindex key entry_3_13 = GramEntries.Block3.entries 3 13 := by
  decide +kernel

theorem entry_reindex_3_14 :
    Integer.Sparse.reindex key entry_3_14 = GramEntries.Block3.entries 3 14 := by
  decide +kernel

theorem entry_reindex_3_15 :
    Integer.Sparse.reindex key entry_3_15 = GramEntries.Block3.entries 3 15 := by
  decide +kernel

theorem entry_reindex_3_16 :
    Integer.Sparse.reindex key entry_3_16 = GramEntries.Block3.entries 3 16 := by
  decide +kernel

theorem entry_reindex_3_17 :
    Integer.Sparse.reindex key entry_3_17 = GramEntries.Block3.entries 3 17 := by
  decide +kernel

theorem entry_reindex_3_18 :
    Integer.Sparse.reindex key entry_3_18 = GramEntries.Block3.entries 3 18 := by
  decide +kernel

theorem entry_reindex_3_19 :
    Integer.Sparse.reindex key entry_3_19 = GramEntries.Block3.entries 3 19 := by
  decide +kernel

theorem entry_reindex_3_20 :
    Integer.Sparse.reindex key entry_3_20 = GramEntries.Block3.entries 3 20 := by
  decide +kernel

theorem entry_reindex_3_21 :
    Integer.Sparse.reindex key entry_3_21 = GramEntries.Block3.entries 3 21 := by
  decide +kernel

theorem entry_reindex_3_22 :
    Integer.Sparse.reindex key entry_3_22 = GramEntries.Block3.entries 3 22 := by
  decide +kernel

theorem entry_reindex_3_23 :
    Integer.Sparse.reindex key entry_3_23 = GramEntries.Block3.entries 3 23 := by
  decide +kernel

theorem entry_reindex_3_24 :
    Integer.Sparse.reindex key entry_3_24 = GramEntries.Block3.entries 3 24 := by
  decide +kernel

theorem entry_reindex_3_25 :
    Integer.Sparse.reindex key entry_3_25 = GramEntries.Block3.entries 3 25 := by
  decide +kernel

theorem entry_reindex_3_26 :
    Integer.Sparse.reindex key entry_3_26 = GramEntries.Block3.entries 3 26 := by
  decide +kernel

theorem entries_reindex_3 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 3 j) = GramEntries.Block3.entries 3 j := by
  fin_cases j
  · exact entry_reindex_3_0
  · exact entry_reindex_3_1
  · exact entry_reindex_3_2
  · exact entry_reindex_3_3
  · exact entry_reindex_3_4
  · exact entry_reindex_3_5
  · exact entry_reindex_3_6
  · exact entry_reindex_3_7
  · exact entry_reindex_3_8
  · exact entry_reindex_3_9
  · exact entry_reindex_3_10
  · exact entry_reindex_3_11
  · exact entry_reindex_3_12
  · exact entry_reindex_3_13
  · exact entry_reindex_3_14
  · exact entry_reindex_3_15
  · exact entry_reindex_3_16
  · exact entry_reindex_3_17
  · exact entry_reindex_3_18
  · exact entry_reindex_3_19
  · exact entry_reindex_3_20
  · exact entry_reindex_3_21
  · exact entry_reindex_3_22
  · exact entry_reindex_3_23
  · exact entry_reindex_3_24
  · exact entry_reindex_3_25
  · exact entry_reindex_3_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex4
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_4_0 :
    Integer.Sparse.reindex key entry_4_0 = GramEntries.Block3.entries 4 0 := by
  decide +kernel

theorem entry_reindex_4_1 :
    Integer.Sparse.reindex key entry_4_1 = GramEntries.Block3.entries 4 1 := by
  decide +kernel

theorem entry_reindex_4_2 :
    Integer.Sparse.reindex key entry_4_2 = GramEntries.Block3.entries 4 2 := by
  decide +kernel

theorem entry_reindex_4_3 :
    Integer.Sparse.reindex key entry_4_3 = GramEntries.Block3.entries 4 3 := by
  decide +kernel

theorem entry_reindex_4_4 :
    Integer.Sparse.reindex key entry_4_4 = GramEntries.Block3.entries 4 4 := by
  decide +kernel

theorem entry_reindex_4_5 :
    Integer.Sparse.reindex key entry_4_5 = GramEntries.Block3.entries 4 5 := by
  decide +kernel

theorem entry_reindex_4_6 :
    Integer.Sparse.reindex key entry_4_6 = GramEntries.Block3.entries 4 6 := by
  decide +kernel

theorem entry_reindex_4_7 :
    Integer.Sparse.reindex key entry_4_7 = GramEntries.Block3.entries 4 7 := by
  decide +kernel

theorem entry_reindex_4_8 :
    Integer.Sparse.reindex key entry_4_8 = GramEntries.Block3.entries 4 8 := by
  decide +kernel

theorem entry_reindex_4_9 :
    Integer.Sparse.reindex key entry_4_9 = GramEntries.Block3.entries 4 9 := by
  decide +kernel

theorem entry_reindex_4_10 :
    Integer.Sparse.reindex key entry_4_10 = GramEntries.Block3.entries 4 10 := by
  decide +kernel

theorem entry_reindex_4_11 :
    Integer.Sparse.reindex key entry_4_11 = GramEntries.Block3.entries 4 11 := by
  decide +kernel

theorem entry_reindex_4_12 :
    Integer.Sparse.reindex key entry_4_12 = GramEntries.Block3.entries 4 12 := by
  decide +kernel

theorem entry_reindex_4_13 :
    Integer.Sparse.reindex key entry_4_13 = GramEntries.Block3.entries 4 13 := by
  decide +kernel

theorem entry_reindex_4_14 :
    Integer.Sparse.reindex key entry_4_14 = GramEntries.Block3.entries 4 14 := by
  decide +kernel

theorem entry_reindex_4_15 :
    Integer.Sparse.reindex key entry_4_15 = GramEntries.Block3.entries 4 15 := by
  decide +kernel

theorem entry_reindex_4_16 :
    Integer.Sparse.reindex key entry_4_16 = GramEntries.Block3.entries 4 16 := by
  decide +kernel

theorem entry_reindex_4_17 :
    Integer.Sparse.reindex key entry_4_17 = GramEntries.Block3.entries 4 17 := by
  decide +kernel

theorem entry_reindex_4_18 :
    Integer.Sparse.reindex key entry_4_18 = GramEntries.Block3.entries 4 18 := by
  decide +kernel

theorem entry_reindex_4_19 :
    Integer.Sparse.reindex key entry_4_19 = GramEntries.Block3.entries 4 19 := by
  decide +kernel

theorem entry_reindex_4_20 :
    Integer.Sparse.reindex key entry_4_20 = GramEntries.Block3.entries 4 20 := by
  decide +kernel

theorem entry_reindex_4_21 :
    Integer.Sparse.reindex key entry_4_21 = GramEntries.Block3.entries 4 21 := by
  decide +kernel

theorem entry_reindex_4_22 :
    Integer.Sparse.reindex key entry_4_22 = GramEntries.Block3.entries 4 22 := by
  decide +kernel

theorem entry_reindex_4_23 :
    Integer.Sparse.reindex key entry_4_23 = GramEntries.Block3.entries 4 23 := by
  decide +kernel

theorem entry_reindex_4_24 :
    Integer.Sparse.reindex key entry_4_24 = GramEntries.Block3.entries 4 24 := by
  decide +kernel

theorem entry_reindex_4_25 :
    Integer.Sparse.reindex key entry_4_25 = GramEntries.Block3.entries 4 25 := by
  decide +kernel

theorem entry_reindex_4_26 :
    Integer.Sparse.reindex key entry_4_26 = GramEntries.Block3.entries 4 26 := by
  decide +kernel

theorem entries_reindex_4 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 4 j) = GramEntries.Block3.entries 4 j := by
  fin_cases j
  · exact entry_reindex_4_0
  · exact entry_reindex_4_1
  · exact entry_reindex_4_2
  · exact entry_reindex_4_3
  · exact entry_reindex_4_4
  · exact entry_reindex_4_5
  · exact entry_reindex_4_6
  · exact entry_reindex_4_7
  · exact entry_reindex_4_8
  · exact entry_reindex_4_9
  · exact entry_reindex_4_10
  · exact entry_reindex_4_11
  · exact entry_reindex_4_12
  · exact entry_reindex_4_13
  · exact entry_reindex_4_14
  · exact entry_reindex_4_15
  · exact entry_reindex_4_16
  · exact entry_reindex_4_17
  · exact entry_reindex_4_18
  · exact entry_reindex_4_19
  · exact entry_reindex_4_20
  · exact entry_reindex_4_21
  · exact entry_reindex_4_22
  · exact entry_reindex_4_23
  · exact entry_reindex_4_24
  · exact entry_reindex_4_25
  · exact entry_reindex_4_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex5
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_5_0 :
    Integer.Sparse.reindex key entry_5_0 = GramEntries.Block3.entries 5 0 := by
  decide +kernel

theorem entry_reindex_5_1 :
    Integer.Sparse.reindex key entry_5_1 = GramEntries.Block3.entries 5 1 := by
  decide +kernel

theorem entry_reindex_5_2 :
    Integer.Sparse.reindex key entry_5_2 = GramEntries.Block3.entries 5 2 := by
  decide +kernel

theorem entry_reindex_5_3 :
    Integer.Sparse.reindex key entry_5_3 = GramEntries.Block3.entries 5 3 := by
  decide +kernel

theorem entry_reindex_5_4 :
    Integer.Sparse.reindex key entry_5_4 = GramEntries.Block3.entries 5 4 := by
  decide +kernel

theorem entry_reindex_5_5 :
    Integer.Sparse.reindex key entry_5_5 = GramEntries.Block3.entries 5 5 := by
  decide +kernel

theorem entry_reindex_5_6 :
    Integer.Sparse.reindex key entry_5_6 = GramEntries.Block3.entries 5 6 := by
  decide +kernel

theorem entry_reindex_5_7 :
    Integer.Sparse.reindex key entry_5_7 = GramEntries.Block3.entries 5 7 := by
  decide +kernel

theorem entry_reindex_5_8 :
    Integer.Sparse.reindex key entry_5_8 = GramEntries.Block3.entries 5 8 := by
  decide +kernel

theorem entry_reindex_5_9 :
    Integer.Sparse.reindex key entry_5_9 = GramEntries.Block3.entries 5 9 := by
  decide +kernel

theorem entry_reindex_5_10 :
    Integer.Sparse.reindex key entry_5_10 = GramEntries.Block3.entries 5 10 := by
  decide +kernel

theorem entry_reindex_5_11 :
    Integer.Sparse.reindex key entry_5_11 = GramEntries.Block3.entries 5 11 := by
  decide +kernel

theorem entry_reindex_5_12 :
    Integer.Sparse.reindex key entry_5_12 = GramEntries.Block3.entries 5 12 := by
  decide +kernel

theorem entry_reindex_5_13 :
    Integer.Sparse.reindex key entry_5_13 = GramEntries.Block3.entries 5 13 := by
  decide +kernel

theorem entry_reindex_5_14 :
    Integer.Sparse.reindex key entry_5_14 = GramEntries.Block3.entries 5 14 := by
  decide +kernel

theorem entry_reindex_5_15 :
    Integer.Sparse.reindex key entry_5_15 = GramEntries.Block3.entries 5 15 := by
  decide +kernel

theorem entry_reindex_5_16 :
    Integer.Sparse.reindex key entry_5_16 = GramEntries.Block3.entries 5 16 := by
  decide +kernel

theorem entry_reindex_5_17 :
    Integer.Sparse.reindex key entry_5_17 = GramEntries.Block3.entries 5 17 := by
  decide +kernel

theorem entry_reindex_5_18 :
    Integer.Sparse.reindex key entry_5_18 = GramEntries.Block3.entries 5 18 := by
  decide +kernel

theorem entry_reindex_5_19 :
    Integer.Sparse.reindex key entry_5_19 = GramEntries.Block3.entries 5 19 := by
  decide +kernel

theorem entry_reindex_5_20 :
    Integer.Sparse.reindex key entry_5_20 = GramEntries.Block3.entries 5 20 := by
  decide +kernel

theorem entry_reindex_5_21 :
    Integer.Sparse.reindex key entry_5_21 = GramEntries.Block3.entries 5 21 := by
  decide +kernel

theorem entry_reindex_5_22 :
    Integer.Sparse.reindex key entry_5_22 = GramEntries.Block3.entries 5 22 := by
  decide +kernel

theorem entry_reindex_5_23 :
    Integer.Sparse.reindex key entry_5_23 = GramEntries.Block3.entries 5 23 := by
  decide +kernel

theorem entry_reindex_5_24 :
    Integer.Sparse.reindex key entry_5_24 = GramEntries.Block3.entries 5 24 := by
  decide +kernel

theorem entry_reindex_5_25 :
    Integer.Sparse.reindex key entry_5_25 = GramEntries.Block3.entries 5 25 := by
  decide +kernel

theorem entry_reindex_5_26 :
    Integer.Sparse.reindex key entry_5_26 = GramEntries.Block3.entries 5 26 := by
  decide +kernel

theorem entries_reindex_5 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 5 j) = GramEntries.Block3.entries 5 j := by
  fin_cases j
  · exact entry_reindex_5_0
  · exact entry_reindex_5_1
  · exact entry_reindex_5_2
  · exact entry_reindex_5_3
  · exact entry_reindex_5_4
  · exact entry_reindex_5_5
  · exact entry_reindex_5_6
  · exact entry_reindex_5_7
  · exact entry_reindex_5_8
  · exact entry_reindex_5_9
  · exact entry_reindex_5_10
  · exact entry_reindex_5_11
  · exact entry_reindex_5_12
  · exact entry_reindex_5_13
  · exact entry_reindex_5_14
  · exact entry_reindex_5_15
  · exact entry_reindex_5_16
  · exact entry_reindex_5_17
  · exact entry_reindex_5_18
  · exact entry_reindex_5_19
  · exact entry_reindex_5_20
  · exact entry_reindex_5_21
  · exact entry_reindex_5_22
  · exact entry_reindex_5_23
  · exact entry_reindex_5_24
  · exact entry_reindex_5_25
  · exact entry_reindex_5_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_6_0 :
    Integer.Sparse.reindex key entry_6_0 = GramEntries.Block3.entries 6 0 := by
  decide +kernel

theorem entry_reindex_6_1 :
    Integer.Sparse.reindex key entry_6_1 = GramEntries.Block3.entries 6 1 := by
  decide +kernel

theorem entry_reindex_6_2 :
    Integer.Sparse.reindex key entry_6_2 = GramEntries.Block3.entries 6 2 := by
  decide +kernel

theorem entry_reindex_6_3 :
    Integer.Sparse.reindex key entry_6_3 = GramEntries.Block3.entries 6 3 := by
  decide +kernel

theorem entry_reindex_6_4 :
    Integer.Sparse.reindex key entry_6_4 = GramEntries.Block3.entries 6 4 := by
  decide +kernel

theorem entry_reindex_6_5 :
    Integer.Sparse.reindex key entry_6_5 = GramEntries.Block3.entries 6 5 := by
  decide +kernel

theorem entry_reindex_6_6 :
    Integer.Sparse.reindex key entry_6_6 = GramEntries.Block3.entries 6 6 := by
  decide +kernel

theorem entry_reindex_6_7 :
    Integer.Sparse.reindex key entry_6_7 = GramEntries.Block3.entries 6 7 := by
  decide +kernel

theorem entry_reindex_6_8 :
    Integer.Sparse.reindex key entry_6_8 = GramEntries.Block3.entries 6 8 := by
  decide +kernel

theorem entry_reindex_6_9 :
    Integer.Sparse.reindex key entry_6_9 = GramEntries.Block3.entries 6 9 := by
  decide +kernel

theorem entry_reindex_6_10 :
    Integer.Sparse.reindex key entry_6_10 = GramEntries.Block3.entries 6 10 := by
  decide +kernel

theorem entry_reindex_6_11 :
    Integer.Sparse.reindex key entry_6_11 = GramEntries.Block3.entries 6 11 := by
  decide +kernel

theorem entry_reindex_6_12 :
    Integer.Sparse.reindex key entry_6_12 = GramEntries.Block3.entries 6 12 := by
  decide +kernel

theorem entry_reindex_6_13 :
    Integer.Sparse.reindex key entry_6_13 = GramEntries.Block3.entries 6 13 := by
  decide +kernel

theorem entry_reindex_6_14 :
    Integer.Sparse.reindex key entry_6_14 = GramEntries.Block3.entries 6 14 := by
  decide +kernel

theorem entry_reindex_6_15 :
    Integer.Sparse.reindex key entry_6_15 = GramEntries.Block3.entries 6 15 := by
  decide +kernel

theorem entry_reindex_6_16 :
    Integer.Sparse.reindex key entry_6_16 = GramEntries.Block3.entries 6 16 := by
  decide +kernel

theorem entry_reindex_6_17 :
    Integer.Sparse.reindex key entry_6_17 = GramEntries.Block3.entries 6 17 := by
  decide +kernel

theorem entry_reindex_6_18 :
    Integer.Sparse.reindex key entry_6_18 = GramEntries.Block3.entries 6 18 := by
  decide +kernel

theorem entry_reindex_6_19 :
    Integer.Sparse.reindex key entry_6_19 = GramEntries.Block3.entries 6 19 := by
  decide +kernel

theorem entry_reindex_6_20 :
    Integer.Sparse.reindex key entry_6_20 = GramEntries.Block3.entries 6 20 := by
  decide +kernel

theorem entry_reindex_6_21 :
    Integer.Sparse.reindex key entry_6_21 = GramEntries.Block3.entries 6 21 := by
  decide +kernel

theorem entry_reindex_6_22 :
    Integer.Sparse.reindex key entry_6_22 = GramEntries.Block3.entries 6 22 := by
  decide +kernel

theorem entry_reindex_6_23 :
    Integer.Sparse.reindex key entry_6_23 = GramEntries.Block3.entries 6 23 := by
  decide +kernel

theorem entry_reindex_6_24 :
    Integer.Sparse.reindex key entry_6_24 = GramEntries.Block3.entries 6 24 := by
  decide +kernel

theorem entry_reindex_6_25 :
    Integer.Sparse.reindex key entry_6_25 = GramEntries.Block3.entries 6 25 := by
  decide +kernel

theorem entry_reindex_6_26 :
    Integer.Sparse.reindex key entry_6_26 = GramEntries.Block3.entries 6 26 := by
  decide +kernel

theorem entries_reindex_6 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 6 j) = GramEntries.Block3.entries 6 j := by
  fin_cases j
  · exact entry_reindex_6_0
  · exact entry_reindex_6_1
  · exact entry_reindex_6_2
  · exact entry_reindex_6_3
  · exact entry_reindex_6_4
  · exact entry_reindex_6_5
  · exact entry_reindex_6_6
  · exact entry_reindex_6_7
  · exact entry_reindex_6_8
  · exact entry_reindex_6_9
  · exact entry_reindex_6_10
  · exact entry_reindex_6_11
  · exact entry_reindex_6_12
  · exact entry_reindex_6_13
  · exact entry_reindex_6_14
  · exact entry_reindex_6_15
  · exact entry_reindex_6_16
  · exact entry_reindex_6_17
  · exact entry_reindex_6_18
  · exact entry_reindex_6_19
  · exact entry_reindex_6_20
  · exact entry_reindex_6_21
  · exact entry_reindex_6_22
  · exact entry_reindex_6_23
  · exact entry_reindex_6_24
  · exact entry_reindex_6_25
  · exact entry_reindex_6_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex7
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_7_0 :
    Integer.Sparse.reindex key entry_7_0 = GramEntries.Block3.entries 7 0 := by
  decide +kernel

theorem entry_reindex_7_1 :
    Integer.Sparse.reindex key entry_7_1 = GramEntries.Block3.entries 7 1 := by
  decide +kernel

theorem entry_reindex_7_2 :
    Integer.Sparse.reindex key entry_7_2 = GramEntries.Block3.entries 7 2 := by
  decide +kernel

theorem entry_reindex_7_3 :
    Integer.Sparse.reindex key entry_7_3 = GramEntries.Block3.entries 7 3 := by
  decide +kernel

theorem entry_reindex_7_4 :
    Integer.Sparse.reindex key entry_7_4 = GramEntries.Block3.entries 7 4 := by
  decide +kernel

theorem entry_reindex_7_5 :
    Integer.Sparse.reindex key entry_7_5 = GramEntries.Block3.entries 7 5 := by
  decide +kernel

theorem entry_reindex_7_6 :
    Integer.Sparse.reindex key entry_7_6 = GramEntries.Block3.entries 7 6 := by
  decide +kernel

theorem entry_reindex_7_7 :
    Integer.Sparse.reindex key entry_7_7 = GramEntries.Block3.entries 7 7 := by
  decide +kernel

theorem entry_reindex_7_8 :
    Integer.Sparse.reindex key entry_7_8 = GramEntries.Block3.entries 7 8 := by
  decide +kernel

theorem entry_reindex_7_9 :
    Integer.Sparse.reindex key entry_7_9 = GramEntries.Block3.entries 7 9 := by
  decide +kernel

theorem entry_reindex_7_10 :
    Integer.Sparse.reindex key entry_7_10 = GramEntries.Block3.entries 7 10 := by
  decide +kernel

theorem entry_reindex_7_11 :
    Integer.Sparse.reindex key entry_7_11 = GramEntries.Block3.entries 7 11 := by
  decide +kernel

theorem entry_reindex_7_12 :
    Integer.Sparse.reindex key entry_7_12 = GramEntries.Block3.entries 7 12 := by
  decide +kernel

theorem entry_reindex_7_13 :
    Integer.Sparse.reindex key entry_7_13 = GramEntries.Block3.entries 7 13 := by
  decide +kernel

theorem entry_reindex_7_14 :
    Integer.Sparse.reindex key entry_7_14 = GramEntries.Block3.entries 7 14 := by
  decide +kernel

theorem entry_reindex_7_15 :
    Integer.Sparse.reindex key entry_7_15 = GramEntries.Block3.entries 7 15 := by
  decide +kernel

theorem entry_reindex_7_16 :
    Integer.Sparse.reindex key entry_7_16 = GramEntries.Block3.entries 7 16 := by
  decide +kernel

theorem entry_reindex_7_17 :
    Integer.Sparse.reindex key entry_7_17 = GramEntries.Block3.entries 7 17 := by
  decide +kernel

theorem entry_reindex_7_18 :
    Integer.Sparse.reindex key entry_7_18 = GramEntries.Block3.entries 7 18 := by
  decide +kernel

theorem entry_reindex_7_19 :
    Integer.Sparse.reindex key entry_7_19 = GramEntries.Block3.entries 7 19 := by
  decide +kernel

theorem entry_reindex_7_20 :
    Integer.Sparse.reindex key entry_7_20 = GramEntries.Block3.entries 7 20 := by
  decide +kernel

theorem entry_reindex_7_21 :
    Integer.Sparse.reindex key entry_7_21 = GramEntries.Block3.entries 7 21 := by
  decide +kernel

theorem entry_reindex_7_22 :
    Integer.Sparse.reindex key entry_7_22 = GramEntries.Block3.entries 7 22 := by
  decide +kernel

theorem entry_reindex_7_23 :
    Integer.Sparse.reindex key entry_7_23 = GramEntries.Block3.entries 7 23 := by
  decide +kernel

theorem entry_reindex_7_24 :
    Integer.Sparse.reindex key entry_7_24 = GramEntries.Block3.entries 7 24 := by
  decide +kernel

theorem entry_reindex_7_25 :
    Integer.Sparse.reindex key entry_7_25 = GramEntries.Block3.entries 7 25 := by
  decide +kernel

theorem entry_reindex_7_26 :
    Integer.Sparse.reindex key entry_7_26 = GramEntries.Block3.entries 7 26 := by
  decide +kernel

theorem entries_reindex_7 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 7 j) = GramEntries.Block3.entries 7 j := by
  fin_cases j
  · exact entry_reindex_7_0
  · exact entry_reindex_7_1
  · exact entry_reindex_7_2
  · exact entry_reindex_7_3
  · exact entry_reindex_7_4
  · exact entry_reindex_7_5
  · exact entry_reindex_7_6
  · exact entry_reindex_7_7
  · exact entry_reindex_7_8
  · exact entry_reindex_7_9
  · exact entry_reindex_7_10
  · exact entry_reindex_7_11
  · exact entry_reindex_7_12
  · exact entry_reindex_7_13
  · exact entry_reindex_7_14
  · exact entry_reindex_7_15
  · exact entry_reindex_7_16
  · exact entry_reindex_7_17
  · exact entry_reindex_7_18
  · exact entry_reindex_7_19
  · exact entry_reindex_7_20
  · exact entry_reindex_7_21
  · exact entry_reindex_7_22
  · exact entry_reindex_7_23
  · exact entry_reindex_7_24
  · exact entry_reindex_7_25
  · exact entry_reindex_7_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex8
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_8_0 :
    Integer.Sparse.reindex key entry_8_0 = GramEntries.Block3.entries 8 0 := by
  decide +kernel

theorem entry_reindex_8_1 :
    Integer.Sparse.reindex key entry_8_1 = GramEntries.Block3.entries 8 1 := by
  decide +kernel

theorem entry_reindex_8_2 :
    Integer.Sparse.reindex key entry_8_2 = GramEntries.Block3.entries 8 2 := by
  decide +kernel

theorem entry_reindex_8_3 :
    Integer.Sparse.reindex key entry_8_3 = GramEntries.Block3.entries 8 3 := by
  decide +kernel

theorem entry_reindex_8_4 :
    Integer.Sparse.reindex key entry_8_4 = GramEntries.Block3.entries 8 4 := by
  decide +kernel

theorem entry_reindex_8_5 :
    Integer.Sparse.reindex key entry_8_5 = GramEntries.Block3.entries 8 5 := by
  decide +kernel

theorem entry_reindex_8_6 :
    Integer.Sparse.reindex key entry_8_6 = GramEntries.Block3.entries 8 6 := by
  decide +kernel

theorem entry_reindex_8_7 :
    Integer.Sparse.reindex key entry_8_7 = GramEntries.Block3.entries 8 7 := by
  decide +kernel

theorem entry_reindex_8_8 :
    Integer.Sparse.reindex key entry_8_8 = GramEntries.Block3.entries 8 8 := by
  decide +kernel

theorem entry_reindex_8_9 :
    Integer.Sparse.reindex key entry_8_9 = GramEntries.Block3.entries 8 9 := by
  decide +kernel

theorem entry_reindex_8_10 :
    Integer.Sparse.reindex key entry_8_10 = GramEntries.Block3.entries 8 10 := by
  decide +kernel

theorem entry_reindex_8_11 :
    Integer.Sparse.reindex key entry_8_11 = GramEntries.Block3.entries 8 11 := by
  decide +kernel

theorem entry_reindex_8_12 :
    Integer.Sparse.reindex key entry_8_12 = GramEntries.Block3.entries 8 12 := by
  decide +kernel

theorem entry_reindex_8_13 :
    Integer.Sparse.reindex key entry_8_13 = GramEntries.Block3.entries 8 13 := by
  decide +kernel

theorem entry_reindex_8_14 :
    Integer.Sparse.reindex key entry_8_14 = GramEntries.Block3.entries 8 14 := by
  decide +kernel

theorem entry_reindex_8_15 :
    Integer.Sparse.reindex key entry_8_15 = GramEntries.Block3.entries 8 15 := by
  decide +kernel

theorem entry_reindex_8_16 :
    Integer.Sparse.reindex key entry_8_16 = GramEntries.Block3.entries 8 16 := by
  decide +kernel

theorem entry_reindex_8_17 :
    Integer.Sparse.reindex key entry_8_17 = GramEntries.Block3.entries 8 17 := by
  decide +kernel

theorem entry_reindex_8_18 :
    Integer.Sparse.reindex key entry_8_18 = GramEntries.Block3.entries 8 18 := by
  decide +kernel

theorem entry_reindex_8_19 :
    Integer.Sparse.reindex key entry_8_19 = GramEntries.Block3.entries 8 19 := by
  decide +kernel

theorem entry_reindex_8_20 :
    Integer.Sparse.reindex key entry_8_20 = GramEntries.Block3.entries 8 20 := by
  decide +kernel

theorem entry_reindex_8_21 :
    Integer.Sparse.reindex key entry_8_21 = GramEntries.Block3.entries 8 21 := by
  decide +kernel

theorem entry_reindex_8_22 :
    Integer.Sparse.reindex key entry_8_22 = GramEntries.Block3.entries 8 22 := by
  decide +kernel

theorem entry_reindex_8_23 :
    Integer.Sparse.reindex key entry_8_23 = GramEntries.Block3.entries 8 23 := by
  decide +kernel

theorem entry_reindex_8_24 :
    Integer.Sparse.reindex key entry_8_24 = GramEntries.Block3.entries 8 24 := by
  decide +kernel

theorem entry_reindex_8_25 :
    Integer.Sparse.reindex key entry_8_25 = GramEntries.Block3.entries 8 25 := by
  decide +kernel

theorem entry_reindex_8_26 :
    Integer.Sparse.reindex key entry_8_26 = GramEntries.Block3.entries 8 26 := by
  decide +kernel

theorem entries_reindex_8 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 8 j) = GramEntries.Block3.entries 8 j := by
  fin_cases j
  · exact entry_reindex_8_0
  · exact entry_reindex_8_1
  · exact entry_reindex_8_2
  · exact entry_reindex_8_3
  · exact entry_reindex_8_4
  · exact entry_reindex_8_5
  · exact entry_reindex_8_6
  · exact entry_reindex_8_7
  · exact entry_reindex_8_8
  · exact entry_reindex_8_9
  · exact entry_reindex_8_10
  · exact entry_reindex_8_11
  · exact entry_reindex_8_12
  · exact entry_reindex_8_13
  · exact entry_reindex_8_14
  · exact entry_reindex_8_15
  · exact entry_reindex_8_16
  · exact entry_reindex_8_17
  · exact entry_reindex_8_18
  · exact entry_reindex_8_19
  · exact entry_reindex_8_20
  · exact entry_reindex_8_21
  · exact entry_reindex_8_22
  · exact entry_reindex_8_23
  · exact entry_reindex_8_24
  · exact entry_reindex_8_25
  · exact entry_reindex_8_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex9
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entry_reindex_9_0 :
    Integer.Sparse.reindex key entry_9_0 = GramEntries.Block3.entries 9 0 := by
  decide +kernel

theorem entry_reindex_9_1 :
    Integer.Sparse.reindex key entry_9_1 = GramEntries.Block3.entries 9 1 := by
  decide +kernel

theorem entry_reindex_9_2 :
    Integer.Sparse.reindex key entry_9_2 = GramEntries.Block3.entries 9 2 := by
  decide +kernel

theorem entry_reindex_9_3 :
    Integer.Sparse.reindex key entry_9_3 = GramEntries.Block3.entries 9 3 := by
  decide +kernel

theorem entry_reindex_9_4 :
    Integer.Sparse.reindex key entry_9_4 = GramEntries.Block3.entries 9 4 := by
  decide +kernel

theorem entry_reindex_9_5 :
    Integer.Sparse.reindex key entry_9_5 = GramEntries.Block3.entries 9 5 := by
  decide +kernel

theorem entry_reindex_9_6 :
    Integer.Sparse.reindex key entry_9_6 = GramEntries.Block3.entries 9 6 := by
  decide +kernel

theorem entry_reindex_9_7 :
    Integer.Sparse.reindex key entry_9_7 = GramEntries.Block3.entries 9 7 := by
  decide +kernel

theorem entry_reindex_9_8 :
    Integer.Sparse.reindex key entry_9_8 = GramEntries.Block3.entries 9 8 := by
  decide +kernel

theorem entry_reindex_9_9 :
    Integer.Sparse.reindex key entry_9_9 = GramEntries.Block3.entries 9 9 := by
  decide +kernel

theorem entry_reindex_9_10 :
    Integer.Sparse.reindex key entry_9_10 = GramEntries.Block3.entries 9 10 := by
  decide +kernel

theorem entry_reindex_9_11 :
    Integer.Sparse.reindex key entry_9_11 = GramEntries.Block3.entries 9 11 := by
  decide +kernel

theorem entry_reindex_9_12 :
    Integer.Sparse.reindex key entry_9_12 = GramEntries.Block3.entries 9 12 := by
  decide +kernel

theorem entry_reindex_9_13 :
    Integer.Sparse.reindex key entry_9_13 = GramEntries.Block3.entries 9 13 := by
  decide +kernel

theorem entry_reindex_9_14 :
    Integer.Sparse.reindex key entry_9_14 = GramEntries.Block3.entries 9 14 := by
  decide +kernel

theorem entry_reindex_9_15 :
    Integer.Sparse.reindex key entry_9_15 = GramEntries.Block3.entries 9 15 := by
  decide +kernel

theorem entry_reindex_9_16 :
    Integer.Sparse.reindex key entry_9_16 = GramEntries.Block3.entries 9 16 := by
  decide +kernel

theorem entry_reindex_9_17 :
    Integer.Sparse.reindex key entry_9_17 = GramEntries.Block3.entries 9 17 := by
  decide +kernel

theorem entry_reindex_9_18 :
    Integer.Sparse.reindex key entry_9_18 = GramEntries.Block3.entries 9 18 := by
  decide +kernel

theorem entry_reindex_9_19 :
    Integer.Sparse.reindex key entry_9_19 = GramEntries.Block3.entries 9 19 := by
  decide +kernel

theorem entry_reindex_9_20 :
    Integer.Sparse.reindex key entry_9_20 = GramEntries.Block3.entries 9 20 := by
  decide +kernel

theorem entry_reindex_9_21 :
    Integer.Sparse.reindex key entry_9_21 = GramEntries.Block3.entries 9 21 := by
  decide +kernel

theorem entry_reindex_9_22 :
    Integer.Sparse.reindex key entry_9_22 = GramEntries.Block3.entries 9 22 := by
  decide +kernel

theorem entry_reindex_9_23 :
    Integer.Sparse.reindex key entry_9_23 = GramEntries.Block3.entries 9 23 := by
  decide +kernel

theorem entry_reindex_9_24 :
    Integer.Sparse.reindex key entry_9_24 = GramEntries.Block3.entries 9 24 := by
  decide +kernel

theorem entry_reindex_9_25 :
    Integer.Sparse.reindex key entry_9_25 = GramEntries.Block3.entries 9 25 := by
  decide +kernel

theorem entry_reindex_9_26 :
    Integer.Sparse.reindex key entry_9_26 = GramEntries.Block3.entries 9 26 := by
  decide +kernel

theorem entries_reindex_9 (j : Fin 27) :
    Integer.Sparse.reindex key (entries 9 j) = GramEntries.Block3.entries 9 j := by
  fin_cases j
  · exact entry_reindex_9_0
  · exact entry_reindex_9_1
  · exact entry_reindex_9_2
  · exact entry_reindex_9_3
  · exact entry_reindex_9_4
  · exact entry_reindex_9_5
  · exact entry_reindex_9_6
  · exact entry_reindex_9_7
  · exact entry_reindex_9_8
  · exact entry_reindex_9_9
  · exact entry_reindex_9_10
  · exact entry_reindex_9_11
  · exact entry_reindex_9_12
  · exact entry_reindex_9_13
  · exact entry_reindex_9_14
  · exact entry_reindex_9_15
  · exact entry_reindex_9_16
  · exact entry_reindex_9_17
  · exact entry_reindex_9_18
  · exact entry_reindex_9_19
  · exact entry_reindex_9_20
  · exact entry_reindex_9_21
  · exact entry_reindex_9_22
  · exact entry_reindex_9_23
  · exact entry_reindex_9_24
  · exact entry_reindex_9_25
  · exact entry_reindex_9_26

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Reindex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block3

theorem entries_reindex (i j : Fin 27) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block3.entries i j := by
  fin_cases i
  · exact entries_reindex_0 j
  · exact entries_reindex_1 j
  · exact entries_reindex_2 j
  · exact entries_reindex_3 j
  · exact entries_reindex_4 j
  · exact entries_reindex_5 j
  · exact entries_reindex_6 j
  · exact entries_reindex_7 j
  · exact entries_reindex_8 j
  · exact entries_reindex_9 j
  · exact entries_reindex_10 j
  · exact entries_reindex_11 j
  · exact entries_reindex_12 j
  · exact entries_reindex_13 j
  · exact entries_reindex_14 j
  · exact entries_reindex_15 j
  · exact entries_reindex_16 j
  · exact entries_reindex_17 j
  · exact entries_reindex_18 j
  · exact entries_reindex_19 j
  · exact entries_reindex_20 j
  · exact entries_reindex_21 j
  · exact entries_reindex_22 j
  · exact entries_reindex_23 j
  · exact entries_reindex_24 j
  · exact entries_reindex_25 j
  · exact entries_reindex_26 j

end MUB6.Certificate.GramAssembly.Block3

end OAI
end

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block3Semantics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators

namespace MUB6.Certificate.GramAssembly.Block3

theorem indexed_entry_eval (i j : Fin 27) (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval (entries i j) (fun k => GramNormalization.eval B (key k)) =
      (GramFunctions.Block3.forms i).mixedGram (GramFunctions.Block3.forms j) B := by
  have he := Integer.Sparse.eval_reindex key (entries i j) (GramNormalization.eval B)
  rw [entries_reindex] at he
  exact he.symm.trans (GramEntries.Block3.entryEval_e i j B hB)

theorem weights_real (i j : Fin 27) :
    (weights i j : ℝ) = realMatrix GramData.Block3.Z i j := by
  change (weights i j : ℝ) = (GramData.Block3.Z i j : ℝ)
  exact_mod_cast weights_cast i j

theorem polynomial_interpretation_e_oai (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval polynomial (fun k => GramNormalization.eval B (key k)) =
      GramNonnegative.quadratic3 B := by
  rw [polynomial_eval_e]
  unfold GramNonnegative.quadratic3
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [indexed_entry_eval i j B hB, weights_real]

end MUB6.Certificate.GramAssembly.Block3

end

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block3.polynomial_interpretation_e_oai
