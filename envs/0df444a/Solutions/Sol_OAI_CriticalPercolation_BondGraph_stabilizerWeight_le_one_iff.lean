-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.stabilizerWeight_le_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:56.536685+00:00
-- url     : https://prove2.me/submissions/62e388c8-6b0a-4ead-b3df-5dbee6904269

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_pos

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularSuperlevels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma stabilizerWeight_le_one_iff_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a x : V) : G.stabilizerWeight a x ≤ 1 ↔ G.stabilizerWeight o x ≤ G.stabilizerWeight o a := by
  rw [G.stabilizerWeight_change_base hc hl o a x]
  conv_rhs => rhs; rw [←mul_one (G.stabilizerWeight o a)]
  exact (ENNReal.mul_le_mul_iff_right (G.stabilizerWeight_pos hc hl o a).ne'
    (G.stabilizerWeight_ne_top o a)).symm

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.stabilizerWeight_le_one_iff_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.stabilizerWeight_le_one_iff_oai.{u_1, u_2}
