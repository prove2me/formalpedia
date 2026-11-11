-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.stabilizerWeight_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:57.494196+00:00
-- url     : https://prove2.me/submissions/bf98db20-48e2-416a-8578-ff65ddb84d89

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

lemma stabilizerWeight_ne_top_oai (o x : V) : G.stabilizerWeight o x ≠ ∞ :=
  ENNReal.ofReal_ne_top

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.stabilizerWeight_ne_top_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.stabilizerWeight_ne_top_oai.{u_1, u_2}
