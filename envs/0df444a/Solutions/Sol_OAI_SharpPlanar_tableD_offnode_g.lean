-- Prove2me | solution 1 for OAI.SharpPlanar.tableD_offnode_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T19:44:58.961614+00:00
-- url     : https://prove2.me/submissions/268ecaf7-0fd7-4c77-a18a-c0a4a74c50fb

import Mathlib
import Definitions.Def_OAIQ098G015
import Theorems.Thm_OAI_SharpPlanar_tableRaw_offnode_g

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
lemma tableD_offnode_g_oai (a : Bool) {n : ℕ} (hn : n%12 ∉ residues) : tableD a n=0 := by
  have hn0 : n≠0 := by intro h; subst n; norm_num [residues] at hn
  simp [tableD,tableRaw_offnode_g hn,hn0]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableD_offnode_g_oai := @OAI.SharpPlanar.tableD_offnode_g_oai
