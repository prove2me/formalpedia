-- Prove2me | solution 1 for OAI.SharpPlanar.tableC_offnode_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:19:52.405196+00:00
-- url     : https://prove2.me/submissions/b9288253-b145-425f-8411-02d5150bcbf4

import Mathlib
import Definitions.Def_OAIQ098E015
import Theorems.Thm_OAI_SharpPlanar_tableRaw_offnode_e

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
lemma tableC_offnode_e_oai (a : Bool) {n : ℕ} (hn : n%12 ∉ residues) : tableC a n=0 := by
  have hn0 : n≠0 := by intro h; subst n; norm_num [residues] at hn
  simp [tableC,tableRaw_offnode_e hn,hn0]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableC_offnode_e_oai := @OAI.SharpPlanar.tableC_offnode_e_oai
