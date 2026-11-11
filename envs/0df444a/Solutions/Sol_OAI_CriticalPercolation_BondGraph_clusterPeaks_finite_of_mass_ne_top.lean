-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.clusterPeaks_finite_of_mass_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:47.896455+00:00
-- url     : https://prove2.me/submissions/38d74449-2148-4dcd-b527-bc58d5f225f1

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_finite_clusterUpperSet_of_mass_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_le_one_iff

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

lemma clusterPeaks_finite_of_mass_ne_top_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (ω : Set E) (v : V) (hm : G.modularMass v (G.cluster ω v) ≠ ∞) :
    (G.clusterPeaks ω v).Finite := by
  apply (G.finite_clusterUpperSet_of_mass_ne_top hm).subset
  intro x hx
  refine ⟨hx.1,?_⟩
  have hh := (G.stabilizerWeight_le_one_iff hc hl v x v).mp (hx.2 v hx.1.symm)
  simpa only [G.stabilizerWeight_self] using hh

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.clusterPeaks_finite_of_mass_ne_top_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.clusterPeaks_finite_of_mass_ne_top_oai.{u_1, u_2}
