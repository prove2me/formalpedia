-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.restriction_incident_subset
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:33.615984+00:00
-- url     : https://prove2.me/submissions/e795a310-6c59-4489-aac3-aaccf37a6634

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_cluster_mono
import Theorems.Thm_OAI_CriticalPercolation_FiniteClusters_restrict_cluster

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedExplorationCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set
open scoped Classical ENNReal

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma restriction_incident_subset_oai (s : Set E) (ω : Set E) (x : V) {e : s}
    (he : e∈(G.restrictEdges s).incidentEdges ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x)) :
    e.val∈G.incidentEdges (G.cluster ω x) := by
  obtain ⟨v,hv,hve⟩ := he
  refine ⟨v,?_,hve⟩
  rw [FiniteClusters.restrict_cluster] at hv
  exact G.cluster_mono Set.inter_subset_right x hv

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.restriction_incident_subset_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.restriction_incident_subset_oai.{u_1, u_2}
