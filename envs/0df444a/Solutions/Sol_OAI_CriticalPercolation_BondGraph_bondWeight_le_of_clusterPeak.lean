-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.bondWeight_le_of_clusterPeak
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:17:44.215249+00:00
-- url     : https://prove2.me/submissions/e98c48a3-ef62-4920-8457-6e59f0a9d33a

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_bondWeight_le_at_end

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

lemma bondWeight_le_of_clusterPeak_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (ω : Set E) (x : V)
    (hp : G.clusterPeak ω x) {e : E} (he : e∈G.incidentEdges (G.cluster ω x)) :
    G.bondWeight x e ≤ (2*K : ℕ) := by
  obtain ⟨v,hv,hve⟩ := he
  exact (G.bondWeight_le_at_end hc hl K hK x v e hve).trans
    (by simpa only [mul_one] using mul_le_mul_right (hp v hv) (2*K : ℕ))

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.bondWeight_le_of_clusterPeak_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.bondWeight_le_of_clusterPeak_oai.{u_1, u_2}
