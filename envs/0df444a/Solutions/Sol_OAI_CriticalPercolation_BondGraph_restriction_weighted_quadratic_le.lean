-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.restriction_weighted_quadratic_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:24:54.248873+00:00
-- url     : https://prove2.me/submissions/b589b53d-99a3-487d-969e-96d40dbf224a

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B002
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_bondWeight_le_of_clusterPeak
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_bondWeight_ne_top
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_restriction_incident_subset
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_weighted_incidence_le
import Theorems.Thm_OAI_CriticalPercolation_IncidenceSearch_tree_quadratic

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_WeightedExplorationCost
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
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

lemma restriction_weighted_quadratic_le_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (s : Set E) [Fintype s]
    (ω : Set E) (x : V) (hp : G.clusterPeak ω x) :
    ENNReal.ofReal ((IncidenceSearch.tree (G.restrictEdges s) x).quadraticCost
      (fun e : s => (G.bondWeight x e.val).toReal) (Subtype.val ⁻¹' ω)) ≤
      (D*(2*K)^2 : ℕ)*G.modularMass x (G.cluster ω x) := by
  rw [IncidenceSearch.tree_quadratic,ENNReal.ofReal_sum_of_nonneg
    (fun e _ => by split_ifs <;> positivity)]
  have hsum : (∑ e : s, if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) ≤
      (D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x) := by
    calc
      _ ≤ ∑ e : s, if e.val∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e.val else 0 := by
        apply Finset.sum_le_sum
        intro e _
        split_ifs with he he'
        · rfl
        · exact False.elim (he' (G.restriction_incident_subset s ω x he))
        · exact zero_le
        · rfl
      _ ≤ ∑' e : E, if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0 := by
        change (∑ e : s, (fun e : E => if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0) e.val) ≤ _
        simpa only [tsum_fintype] using
          (ENNReal.tsum_comp_le_tsum_of_injective (f := (Subtype.val : s → E)) Subtype.val_injective
            (fun e : E => if e∈G.incidentEdges (G.cluster ω x) then G.bondWeight x e else 0))
      _ ≤ _ := G.weighted_incidence_le hc hl D K hD hK x _
  calc
    _ ≤ ∑ e : s, (2*K : ℕ)*(if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) := by
      apply Finset.sum_le_sum
      intro e _
      split_ifs with he
      · rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (G.bondWeight_ne_top x e.val),pow_two]
        exact mul_le_mul_left (G.bondWeight_le_of_clusterPeak hc hl K hK ω x hp
          (G.restriction_incident_subset s ω x he)) _
      · simp
    _ = (2*K : ℕ)*(∑ e : s, if e∈(G.restrictEdges s).incidentEdges
        ((G.restrictEdges s).cluster (Subtype.val ⁻¹' ω) x) then G.bondWeight x e.val else 0) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2*K : ℕ)*((D*(2*K) : ℕ)*G.modularMass x (G.cluster ω x)) := mul_le_mul_right hsum _
    _ = _ := by simp only [Nat.cast_mul,Nat.cast_pow] <;> ring

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.restriction_weighted_quadratic_le_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.restriction_weighted_quadratic_le_oai.{u_1, u_2}
