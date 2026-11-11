-- Prove2me | solution 1 for OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T17:21:09.497862+00:00
-- url     : https://prove2.me/submissions/073fc096-3869-4fe3-90e9-e46043fd000e

import Mathlib
import Definitions.Def_CriticalPercolation
import Definitions.Def_OAIQ228B000
import Theorems.Thm_OAI_CriticalPercolation_BondGraph_stabilizerWeight_change_base

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

lemma bondWeight_change_base (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (o a : V) (e : E) : G.bondWeight o e = G.stabilizerWeight o a * G.bondWeight a e := by
  unfold bondWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact G.stabilizerWeight_change_base hc hl o a v

lemma incidence_stabilizerOrbit_subset_ball (v w : V) (n : ℕ) (hw : w∈G.vertexBall v n) :
    G.stabilizerOrbit v w ⊆ G.vertexBall v n := by
  intro z hz
  obtain ⟨φ,hv,hwz⟩ := G.mem_stabilizerOrbit.mp hz
  have h := (Aut.vertexBall_mem G φ v w n).mpr hw
  simpa only [hv,hwz] using h

lemma stabilizerWeight_le_ball_bound (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) {v w : V}
    (_hw : w∈G.vertexBall v 1) (hv : v∈G.vertexBall w 1) :
    G.stabilizerWeight v w ≤ K := by
  unfold stabilizerWeight modularRatio
  apply ENNReal.ofReal_le_of_le_toReal
  simp only [ENNReal.toReal_natCast]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (G.suborbitCard_pos hc hl v w))).mpr
  have hnum : G.suborbitCard w v ≤ K :=
    (Set.ncard_le_ncard (G.incidence_stabilizerOrbit_subset_ball w v 1 hv)
      (G.vertexBall_finite hl w 1)).trans (hK w)
  have hden : (1:ℝ)≤G.suborbitCard v w := by exact_mod_cast G.suborbitCard_pos hc hl v w
  exact (Nat.cast_le.mpr hnum).trans (by nlinarith [show (0:ℝ)≤K by positivity])

lemma common_bond_ball_one {v w : V} {e : E} (hv : v∈G.ends e) (hw : w∈G.ends e) :
    w∈G.vertexBall v 1 := by
  by_cases he : v=w
  · subst w
    exact G.mem_vertexBall_self v 1
  · apply G.vertexBall_step (G.mem_vertexBall_self v 0)
    apply (SimpleGraph.fromEdgeSet_adj _).mpr
    refine ⟨?_,he⟩
    refine ⟨e,Set.mem_univ e,?_⟩
    exact (Sym2.mem_and_mem_iff he).mp ⟨hv,hw⟩

lemma bondWeight_le_at_end_oai (hc : G.fullGraph.Connected) (hl : G.LocallyFinite)
    (K : ℕ) (hK : ∀ v, (G.vertexBall v 1).ncard≤K) (o v : V) (e : E)
    (hv : v∈G.ends e) : G.bondWeight o e ≤ (2*K : ℕ)*G.stabilizerWeight o v := by
  rw [G.bondWeight_change_base hc hl o v]
  have hsum : G.bondWeight v e ≤ (2*K : ℕ) := by
    calc
      _ ≤ ∑ w∈(G.ends e).toFinset, (K : ℝ≥0∞) := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' : w∈G.ends e := Sym2.mem_toFinset.mp hw
        exact G.stabilizerWeight_le_ball_bound hc hl K hK
          (G.common_bond_ball_one hv hw') (G.common_bond_ball_one hw' hv)
      _ = ((G.ends e).toFinset.card * K : ℕ) := by simp [nsmul_eq_mul]
      _ ≤ (2*K : ℕ) := by
        have hh : (G.ends e).toFinset.card≤2 := by
          rw [Sym2.card_toFinset]
          split_ifs <;> omega
        exact_mod_cast Nat.mul_le_mul_right K hh
  calc _ ≤ G.stabilizerWeight o v * (2*K : ℕ) := by gcongr
       _ = _ := mul_comm _ _

end CriticalPercolation.BondGraph
end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end_oai.{u_1, u_2} := @OAI.CriticalPercolation.BondGraph.bondWeight_le_at_end_oai.{u_1, u_2}
