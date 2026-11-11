-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.bondWeight_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:42.799441+00:00
-- url     : https://prove2.me/submissions/cf9ccc84-a924-4e63-a4ff-99fe3f5d8220

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularIncidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma bondWeight_ne_top_oai (o : V) (e : E) : G.bondWeight o e ≠ ∞ := by
  apply ENNReal.sum_ne_top.mpr
  intro v hv
  exact G.stabilizerWeight_ne_top o v

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.bondWeight_ne_top_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.bondWeight_ne_top_oai.{u_1, u_2}
