-- Prove2me | solution 1 for OAI.SharpPlanar.tableRaw_offnode_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:20:16.310204+00:00
-- url     : https://prove2.me/submissions/b607bd94-3290-49be-86b9-69db51e8f747

import Mathlib
import Definitions.Def_OAIQ098E015

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
lemma tableRaw_offnode_e_oai {n : ℕ} (hn : n%12 ∉ residues) : tableRaw n=(0,0,0,0) := by
  unfold tableRaw
  split <;> (first | (solve | norm_num [residues] at hn) | rfl)
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableRaw_offnode_e_oai := @OAI.SharpPlanar.tableRaw_offnode_e_oai
