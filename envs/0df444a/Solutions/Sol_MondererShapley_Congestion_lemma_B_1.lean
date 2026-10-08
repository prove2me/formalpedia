-- Prove2me | solution 1 for MondererShapley.Congestion.lemma_B_1
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:00:48.311644+00:00
-- url     : https://prove2.me/submissions/d9df77a4-1929-44d9-adc0-aba7ed2032c3

import Mathlib
import Definitions.Def_CongestionPoA_AsymSum_Model
import Definitions.Def_MondererShapley_Congestion_congestionPayoff

open CongestionPoA.AsymSum MondererShapley.Congestion

theorem solution {ι M : Type*} [Fintype ι] [DecidableEq ι] [Fintype M] [DecidableEq M]
    (G : CongestionGame ι M) (i : ι) (A : ∀ k, ↥(G.strategies k)) :
    congestionPayoff G i A =
      ∑ r ∈ Finset.Icc 1 (Fintype.card ι),
        ∑ j ∈ Finset.univ.filter (fun j : M => ∃ S : Finset ι, i ∈ S ∧ S.card = r ∧
            (∀ k ∈ S, j ∈ (A k : Finset M)) ∧ ∀ k ∉ S, j ∉ (A k : Finset M)),
          G.latency j r := by
  classical
  have hc (j : M) (r : ℕ) :
      (∃ S : Finset ι, i ∈ S ∧ S.card = r ∧
          (∀ k ∈ S, j ∈ (A k : Finset M)) ∧ ∀ k ∉ S, j ∉ (A k : Finset M)) ↔
      j ∈ (A i : Finset M) ∧ load (fun k => (A k : Finset M)) j = r := by
    constructor
    · rintro ⟨S, hi, hr, hyes, hno⟩
      refine ⟨hyes i hi, ?_⟩
      have hs : Finset.univ.filter (fun k => j ∈ (A k : Finset M)) = S := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => by_contra fun hn => hno k hn h, hyes k⟩
      simpa [load, hs] using hr
    · rintro ⟨hi, hr⟩
      refine ⟨Finset.univ.filter (fun k => j ∈ (A k : Finset M)), by simpa using hi,
        hr, ?_, ?_⟩
      · intro k hk; simpa using hk
      · intro k hk; simpa using hk
  unfold congestionPayoff cost
  simp_rw [hc, Finset.sum_filter]
  rw [Finset.sum_comm]
  rw [← Finset.sum_subset (Finset.subset_univ (A i).val) (by
    intro j _ hj
    simp [hj])]
  apply Finset.sum_congr rfl
  intro j hj
  have hi : j ∈ (A i : Finset M) := hj
  have hl : load (fun k => (A k : Finset M)) j ∈ Finset.Icc 1 (Fintype.card ι) := by
    simp only [Finset.mem_Icc, load]
    constructor
    · exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
    · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  simp [hi, Finset.sum_ite_eq', hl]

#print axioms solution
