-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:13.165041+00:00
-- url     : https://prove2.me/submissions/a9c9b86c-54af-44bb-8a76-2bbcadbf8254

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

lemma stabilizerWeight_change_base_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight o x =
      G.stabilizerWeight o a * G.stabilizerWeight a x := by
  unfold stabilizerWeight
  rw [←ENNReal.ofReal_mul (G.modularRatio_pos hc hl a o).le]
  congr 1
  rw [mul_comm,G.modularRatio_cocycle hc hl]

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.stabilizerWeight_change_base_oai.{u_1, u_2}
