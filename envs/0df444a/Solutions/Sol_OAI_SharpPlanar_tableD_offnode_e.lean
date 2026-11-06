-- Prove2me | solution 1 for OAI.SharpPlanar.tableD_offnode_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:19:53.607105+00:00
-- url     : https://prove2.me/submissions/bbae3d1e-b219-4c1b-93c2-e82233849d9c

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
lemma tableD_offnode_e_oai (a : Bool) {n : ℕ} (hn : n%12 ∉ residues) : tableD a n=0 := by
  have hn0 : n≠0 := by intro h; subst n; norm_num [residues] at hn
  simp [tableD,tableRaw_offnode_e hn,hn0]
end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.tableD_offnode_e_oai := @OAI.SharpPlanar.tableD_offnode_e_oai
