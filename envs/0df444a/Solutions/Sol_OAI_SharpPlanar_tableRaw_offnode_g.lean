-- Prove2me | solution 1 for OAI.SharpPlanar.tableRaw_offnode_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:45:01.770618+00:00
-- url     : https://prove2.me/submissions/c187eb05-a037-4ed8-9772-d2f3e066eda7

import Mathlib
import Definitions.Def_OAIQ098G015

section
-- module Solutions.OAIQ098_PP.PlanarPacking_TableDensityBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Cardinal densities and finite coefficient families

The finite coefficient densities agree with the cardinal densities of the corresponding data.
-/

namespace SharpPlanar
open MeasureTheory
open scoped BigOperators
lemma tableRaw_offnode_g_oai {n : ℕ} (hn : n%12 ∉ residues) : tableRaw n=(0,0,0,0) := by
  unfold tableRaw
  split <;> (first | (solve | norm_num [residues] at hn) | rfl)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableRaw_offnode_g_oai := @OAI.SharpPlanar.tableRaw_offnode_g_oai
