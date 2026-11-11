-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:18:56.525327+00:00
-- url     : https://prove2.me/submissions/c8e56c8c-eded-4696-b5bd-ba5d38158397

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

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

lemma finite_clusterUpperSet_of_mass_ne_top_oai {ω : Set E} {v : V}
    (hm : G.modularMass v (G.cluster ω v) ≠ ∞) : (G.clusterUpperSet ω v).Finite := by
  apply (ENNReal.finite_const_le_of_tsum_ne_top hm (ε := 1) one_ne_zero).subset
  intro x hx
  change 1 ≤ if x∈G.cluster ω v then G.stabilizerWeight v x else 0
  rw [ite_eq_left hx.1]
  exact hx.2

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.finite_clusterUpperSet_of_mass_ne_top_oai.{u_1, u_2}
