-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:20:42.250027+00:00
-- url     : https://prove2.me/submissions/5d0eeda2-60d8-4406-b99e-91d2c09139d1

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularSuperlevels
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma mem_clusterUpperSet_self_oai (ω : Set E) (v : V) : v∈G.clusterUpperSet ω v := by
  exact ⟨SimpleGraph.Reachable.refl v,by simp⟩

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.mem_clusterUpperSet_self_oai.{u_1, u_2}
