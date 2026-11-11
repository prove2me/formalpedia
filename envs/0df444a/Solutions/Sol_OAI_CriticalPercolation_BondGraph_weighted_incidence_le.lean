-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.weighted_incidence_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:22:36.273441+00:00
-- url     : https://prove2.me/submissions/72379e5b-4a3f-41a5-bb20-c3632b67f28b

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_bondWeight_le_at_end

section
-- module Solutions.Q228_CP.CriticalPercolation_Modular_ModularIncidence
attribute [-simp] _root_.OAI.CriticalPercolation.BondGraph.modularCharacter_apply _root_.OAI.CriticalPercolation.BondGraph.modularCoordinate_val _root_.OAI.CriticalPercolation.BondGraph.swapPairOrbit_mk
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped Classical ENNReal BigOperators

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma weighted_incidence_le_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (D K : ℕ) (hD : ∀ v, (G.incidentEdges {v}).ncard≤D)
    (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o : V) (S : Set V) :
    (∑' e : E, if e∈G.incidentEdges S then G.bondWeight o e else 0) ≤
      (D*(2*K) : ℕ)*G.modularMass o S := by
  calc
    _ ≤ ∑' e : E, ∑' v : V, if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0 := by
      apply ENNReal.tsum_le_tsum
      intro e
      by_cases he : e∈G.incidentEdges S
      · rw [ite_eq_left he]
        obtain ⟨v,hv,hve⟩ := he
        simpa only [ite_eq_left (show v∈S ∧ v∈G.ends e from ⟨hv,hve⟩)] using
          (ENNReal.le_tsum v (f := fun v => if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0))
      · simp only [ite_eq_right he]; exact zero_le
    _ = ∑' v : V, ∑' e : E, if v∈S ∧ v∈G.ends e then G.bondWeight o e else 0 :=
      ENNReal.tsum_comm
    _ ≤ ∑' v : V, if v∈S then (D*(2*K) : ℕ)*G.stabilizerWeight o v else 0 := by
      apply ENNReal.tsum_le_tsum
      intro v
      by_cases hv : v∈S
      · simp only [hv,true_and,ite_true, if_true]
        have hf : (G.incidentEdges {v}).Finite := by simpa [incidentEdges] using hl v
        have hm (e : E) : e∈G.incidentEdges {v} ↔ v∈G.ends e := by
          simp [incidentEdges]
        have ht : (∑' e : E, if v∈G.ends e then G.bondWeight o e else 0) =
            ∑ e∈hf.toFinset, G.bondWeight o e := by
          rw [tsum_eq_sum (s := hf.toFinset) (fun e he => by
            simp only [hf.mem_toFinset,hm] at he
            exact ite_eq_right he)]
          apply Finset.sum_congr rfl
          intro e he
          exact ite_eq_left ((hm e).mp (hf.mem_toFinset.mp he))
        rw [ht]
        calc
          _ ≤ ∑ e∈hf.toFinset, (2*K : ℕ)*G.stabilizerWeight o v := by
            apply Finset.sum_le_sum
            intro e he
            exact G.bondWeight_le_at_end hc hl K hK o v e ((hm e).mp (hf.mem_toFinset.mp he))
          _ = ((G.incidentEdges {v}).ncard : ℝ≥0∞)*((2*K : ℕ)*G.stabilizerWeight o v) := by
            simp only [Finset.sum_const,nsmul_eq_mul,←Set.ncard_eq_toFinset_card _ hf]
          _ ≤ (D : ℝ≥0∞)*((2*K : ℕ)*G.stabilizerWeight o v) := by
            gcongr
            exact_mod_cast hD v
          _ = _ := by simp only [Nat.cast_mul,mul_assoc]
      · simp only [hv,false_and,ite_false, if_false,tsum_zero,le_refl]
    _ = _ := by
      unfold modularMass
      rw [←ENNReal.tsum_mul_left]
      apply tsum_congr
      intro v
      split_ifs <;> simp

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.weighted_incidence_le_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.weighted_incidence_le_oai.{u_1, u_2}
