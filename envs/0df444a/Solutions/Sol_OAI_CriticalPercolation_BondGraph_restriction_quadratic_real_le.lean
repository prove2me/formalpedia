-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.restriction_quadratic_real_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:53.364555+00:00
-- url     : https://prove2.me/submissions/b122f136-29df-43d5-8574-b76cd17d02a3

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_restriction_weighted_quadratic_le

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

lemma restriction_quadratic_real_le_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (s : Set E) [Fintype s]
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x)
    (U : ℝ) (hU : 0≤U) (hm : G.modularMass x (G.cluster ω x)≤ENNReal.ofReal U) :
    (IncidenceSearch.tree (G.restrictEdges s) x).quadraticCost
      (fun e : s => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω) ≤ (D*(2*K)^2 : ℕ)*U := by
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
  calc _ ≤ (D*(2*K)^2 : ℕ)*G.modularMass x (G.cluster ω x) :=
        G.restriction_weighted_quadratic_le hc hl D K hD hK s ω x hp
       _ ≤ (D*(2*K)^2 : ℕ)*ENNReal.ofReal U := mul_le_mul_right hm _
       _ = _ := by rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast]

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.restriction_quadratic_real_le_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.restriction_quadratic_real_le_oai.{u_1, u_2}
