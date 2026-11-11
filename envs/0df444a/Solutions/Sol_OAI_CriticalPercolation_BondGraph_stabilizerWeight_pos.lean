-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.stabilizerWeight_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:14.186859+00:00
-- url     : https://prove2.me/submissions/2caaa85e-2e26-4410-b5c9-f8c945e6f439

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularClusterMass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_pos_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o x : V) : 0 < G.stabilizerWeight o x :=
  ENNReal.ofReal_pos.mpr (G.modularRatio_pos hc hl x o)

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.stabilizerWeight_pos_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.stabilizerWeight_pos_oai.{u_1, u_2}
