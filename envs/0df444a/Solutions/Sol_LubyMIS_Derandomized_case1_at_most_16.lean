-- Prove2me | solution 1 for LubyMIS.Derandomized.case1_at_most_16
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:31:33.072392+00:00
-- url     : https://prove2.me/submissions/9def471b-324c-4c58-bbad-a035804798bd

import Mathlib
import Definitions.Def_LubyMIS_Derandomized_Basic
import Definitions.Def_LubyMIS_Derandomized_AlgorithmD

namespace LubyMIS.Derandomized

theorem aux_c1m16_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U : Finset (Fin n)) (i : Fin n) (hi : i ∈ V1 G U) :
    (V1 G U \ ({i} ∪ (restrict G U).neighborFinset i)).card + 1 + (restrict G U).degree i
      ≤ U.card := by
  have hV : V1 G U ⊆ U := Finset.sdiff_subset
  have hiU : i ∈ U := hV hi
  have hN : (restrict G U).neighborFinset i ⊆ U := by
    intro j hj
    rw [SimpleGraph.mem_neighborFinset] at hj
    exact hj.2.1
  have hA : ({i} ∪ (restrict G U).neighborFinset i) ⊆ U :=
    Finset.union_subset (Finset.singleton_subset_iff.mpr hiU) hN
  have hnot : i ∉ (restrict G U).neighborFinset i := by
    rw [SimpleGraph.mem_neighborFinset]
    exact (restrict G U).irrefl
  have hcardA : ({i} ∪ (restrict G U).neighborFinset i).card = 1 + (restrict G U).degree i := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hnot),
      Finset.card_singleton, SimpleGraph.card_neighborFinset_eq_degree]
  have h1 := Finset.card_sdiff_add_card (V1 G U) ({i} ∪ (restrict G U).neighborFinset i)
  have h2 : (V1 G U ∪ ({i} ∪ (restrict G U).neighborFinset i)).card ≤ U.card :=
    Finset.card_le_card (Finset.union_subset hV hA)
  omega

theorem aux_c1m16_inv (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (s : ℕ → Finset (Fin n) × Finset (Fin n)) (hs : IsRun G q s) (K : ℕ) :
    (16 + n) * ((Finset.range K).filter
      (fun k => (∀ j ≤ k, (s j).2.Nonempty) ∧ Case1 G (s k))).card
      + 16 * (if (∀ j < K, (s j).2.Nonempty) then (s K).2.card else 0) ≤ 16 * n := by
  induction K with
  | zero =>
    simp [hs.1]
  | succ K ih =>
    by_cases hP : (∀ j < K, (s j).2.Nonempty) ∧ (s K).2.Nonempty
    · have hP1 : ∀ j < K + 1, (s j).2.Nonempty := by
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact hP.1 j h
        · subst h; exact hP.2
      have hle : ∀ j ≤ K, (s j).2.Nonempty := fun j hj => hP1 j (Nat.lt_succ_of_le hj)
      rw [if_pos hP1]
      rw [if_pos hP.1] at ih
      have hstep := hs.2 K hP.2
      by_cases hc : Case1 G (s K)
      · rw [Finset.range_add_one, Finset.filter_insert, if_pos ⟨hle, hc⟩,
          Finset.card_insert_of_notMem (by simp)]
        obtain ⟨i, hi, -, hdeg, ht⟩ : ∃ i ∈ V1 G (s K).2,
            (∀ j ∈ V1 G (s K).2, (restrict G (s K).2).degree j ≤ (restrict G (s K).2).degree i) ∧
            n ≤ 16 * (restrict G (s K).2).degree i ∧
            s (K + 1) = ((s K).1 ∪ zeroSet G (s K).2 ∪ {i},
              V1 G (s K).2 \ ({i} ∪ (restrict G (s K).2).neighborFinset i)) := by
          rcases hstep with h | h
          · exact h
          · exfalso
            obtain ⟨i, hi, hd⟩ := hc
            have := h.1 i hi
            omega
        have hcard := aux_c1m16_card G (s K).2 i hi
        rw [ht]
        dsimp only
        nlinarith
      · rw [Finset.range_add_one, Finset.filter_insert, if_neg (fun h => hc h.2)]
        have hsub : (s (K + 1)).2 ⊆ (s K).2 := by
          rcases hstep with ⟨i, hi, -, -, ht⟩ | ⟨-, x, y, -, ht⟩
          · rw [ht]; exact Finset.sdiff_subset.trans Finset.sdiff_subset
          · rw [ht]; exact Finset.sdiff_subset.trans Finset.sdiff_subset
        have := Finset.card_le_card hsub
        nlinarith
    · have hP1 : ¬ ∀ j < K + 1, (s j).2.Nonempty := by
        intro h
        exact hP ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h K (Nat.lt_succ_self K)⟩
      rw [if_neg hP1, Finset.range_add_one, Finset.filter_insert, if_neg]
      · have h0 : 0 ≤ 16 * (if (∀ j < K, (s j).2.Nonempty) then (s K).2.card else 0) :=
          Nat.zero_le _
        omega
      · rintro ⟨h, -⟩
        exact hP ⟨fun j hj => h j hj.le, h K le_rfl⟩

end LubyMIS.Derandomized

open LubyMIS.Derandomized

theorem solution (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (q : ℕ)
    (hq : q.Prime) (hnq : n ≤ q) (hq2 : q ≤ 2 * n) (s : ℕ → Finset (Fin n) × Finset (Fin n))
    (hs : IsRun G q s) (K : ℕ) :
    ((Finset.range K).filter
      (fun k => (∀ j ≤ k, (s j).2.Nonempty) ∧ Case1 G (s k))).card ≤ 16 := by
  have h := aux_c1m16_inv n G q s hs K
  by_contra hc
  rw [not_le] at hc
  have h17 : (16 + n) * 17 ≤ (16 + n) * ((Finset.range K).filter
      (fun k => (∀ j ≤ k, (s j).2.Nonempty) ∧ Case1 G (s k))).card :=
    Nat.mul_le_mul_left _ hc
  omega
