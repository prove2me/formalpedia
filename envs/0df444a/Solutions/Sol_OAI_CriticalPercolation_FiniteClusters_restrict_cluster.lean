-- Prove2me | solution 1 for OAI.CriticalPercolation.FiniteClusters.restrict_cluster
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:37.419199+00:00
-- url     : https://prove2.me/submissions/bce456c3-d7a2-492d-b6e2-01ca421751bb

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000

section
-- module Solutions.Q228_CP.CriticalPercolation_GraphGeometry_HitEvent
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped BigOperators
open Set MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
open Set
open scoped Classical
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation.BondGraph
open CriticalPercolation.FiniteProduct CriticalPercolation.ClusterDeletion
open CriticalPercolation.ClusterColumns CriticalPercolation.BernoulliProduct

variable {V E : Type*} (G : BondGraph V E)

lemma restrictEdges_openGraph (s : Set E) (ω : Set E) :
    (G.restrictEdges s).openGraph (Subtype.val ⁻¹' ω) = G.openGraph (s ∩ ω) := by
  unfold openGraph restrictEdges
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, Set.mem_inter_iff, Subtype.exists]
  constructor
  · rintro ⟨e, hs, hω, rfl⟩
    exact ⟨e, ⟨hs, hω⟩, rfl⟩
  · rintro ⟨e, ⟨hs, hω⟩, rfl⟩
    exact ⟨e, hs, hω, rfl⟩

end CriticalPercolation.BondGraph

open Set MeasureTheory ProbabilityTheory
open scoped Classical

end
end

end OAI
end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ClusterMassRestriction
attribute [-instance] _root_.OAI.CriticalPercolation.BondGraph.instGroupAut _root_.OAI.CriticalPercolation.BondGraph.instMulActionAut _root_.OAI.CriticalPercolation.BondGraph.law_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory Filter
open scoped Classical BigOperators Topology

namespace CriticalPercolation.FiniteClusters
variable {V E : Type*} (G : BondGraph V E)

lemma restrict_cluster_oai (K : Set E) (ω : Set E) (v : V) :
    (G.restrictEdges K).cluster (Subtype.val ⁻¹' ω) v = G.cluster (K ∩ ω) v := by
  simp only [BondGraph.cluster,G.restrictEdges_openGraph]

end CriticalPercolation.FiniteClusters
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.FiniteClusters.restrict_cluster_oai.{u_1, u_2} := @OAI.CriticalPercolation.FiniteClusters.restrict_cluster_oai.{u_1, u_2}
