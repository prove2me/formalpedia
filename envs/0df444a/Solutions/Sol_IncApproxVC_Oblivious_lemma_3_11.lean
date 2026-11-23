-- Prove2me | solution 1 for IncApproxVC.Oblivious.lemma_3_11
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:59:00.032833+00:00
-- url     : https://prove2.me/submissions/fbd7f8e8-894a-47c6-ba00-69fd42f1b339

import Definitions.Def_IncApproxVC_Oblivious_Digraph
import Definitions.Def_IncApproxVC_Oblivious_Cuts

namespace Aux311

lemma vol_univ_eq_numEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : IncApproxVC.Oblivious.Digraph V) (hG : G.Loopless) :
    G.vol Finset.univ = G.numEdges := by
  unfold IncApproxVC.Oblivious.Digraph.vol IncApproxVC.Oblivious.Digraph.outDeg
    IncApproxVC.Oblivious.Digraph.outBoundary IncApproxVC.Oblivious.Digraph.edgesBetween
    IncApproxVC.Oblivious.Digraph.numEdges
  have h1 : ∀ v : V,
      G.edges.filter (fun e => e.1 ∈ ({v} : Finset V) ∧ e.2 ∈ ({v} : Finset V)ᶜ) =
      G.edges.filter (fun e => e.1 = v) := by
    intro v
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_compl, and_congr_right_iff]
    intro he
    exact ⟨fun h => h.1, fun hv => ⟨hv, fun h2 => hG e he (hv.trans h2.symm)⟩⟩
  simp_rw [h1]
  exact (Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := G.edges) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)).symm

end Aux311

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : IncApproxVC.Oblivious.Digraph V) (hG : G.Loopless)
    (s : V) (k : ℕ) (hk : 1 ≤ k) (ν ε : ℝ) (hν : 0 < ν) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hm : 2 * ν < ε * (G.numEdges : ℝ)) :
    (∀ S : Finset V, s ∈ S → IncApproxVC.Oblivious.Digraph.IsEdgeCut S Sᶜ →
        (G.outBoundary S).card ≤ k →
        (G.vol S : ℝ) ≤ ν → G.penaltyScore (ε * k / ν) S ≤ (1 + ε) * k) ∧
      (∀ S : Finset V, s ∈ S → G.penaltyScore (ε * k / ν) S ≤ (1 + ε) * k →
        IncApproxVC.Oblivious.Digraph.IsEdgeCut S Sᶜ ∧
          ((G.outBoundary S).card : ℝ) ≤ (1 + ε) * k ∧
          (G.vol S : ℝ) ≤ 2 * ν / ε) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  constructor
  · intro S _ _ hcard hvol
    unfold IncApproxVC.Oblivious.Digraph.penaltyScore
    have hcard' : ((G.outBoundary S).card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcard
    have hα_nonneg : 0 ≤ ε * (k : ℝ) / ν := by positivity
    have hmul : (ε * (k : ℝ) / ν) * (G.vol S : ℝ) ≤ (ε * (k : ℝ) / ν) * ν :=
      mul_le_mul_of_nonneg_left hvol hα_nonneg
    have hsimp : (ε * (k : ℝ) / ν) * ν = ε * (k : ℝ) := div_mul_cancel₀ _ (ne_of_gt hν)
    linarith
  · intro S hs hscore
    unfold IncApproxVC.Oblivious.Digraph.penaltyScore at hscore
    have hvol_nonneg : (0 : ℝ) ≤ (G.vol S : ℝ) := Nat.cast_nonneg _
    have hcard_nonneg : (0 : ℝ) ≤ ((G.outBoundary S).card : ℝ) := Nat.cast_nonneg _
    have hpen_nonneg : 0 ≤ (ε * (k : ℝ) / ν) * (G.vol S : ℝ) := by positivity
    have hcard_le : ((G.outBoundary S).card : ℝ) ≤ (1 + ε) * (k : ℝ) := by linarith
    have hvol_le : (G.vol S : ℝ) ≤ 2 * ν / ε := by
      have h1 : (ε * (k : ℝ) / ν) * (G.vol S : ℝ) ≤ (1 + ε) * (k : ℝ) := by linarith
      have h2 : (1 + ε) * (k : ℝ) ≤ 2 * (k : ℝ) := by nlinarith
      have h3 : (ε * (k : ℝ) / ν) * (G.vol S : ℝ) ≤ 2 * (k : ℝ) := le_trans h1 h2
      rw [div_mul_eq_mul_div, div_le_iff₀ hν] at h3
      rw [le_div_iff₀ hε0]
      nlinarith
    have hSc_nonempty : Sᶜ.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hSc
      have hSuniv : S = Finset.univ := by
        simpa using congrArg Compl.compl hSc
      rw [hSuniv, Aux311.vol_univ_eq_numEdges G hG] at hvol_le
      rw [le_div_iff₀ hε0] at hvol_le
      linarith
    refine ⟨⟨Finset.union_compl S, disjoint_compl_right, ⟨s, hs⟩, hSc_nonempty⟩, hcard_le, hvol_le⟩
