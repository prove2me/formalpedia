-- Prove2me | solution 1 for HyperKCut.Structure.claim_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T15:16:13.566365+00:00
-- url     : https://prove2.me/submissions/38425ae9-698a-4d74-9ca8-1f1acecfeb55

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

open HyperKCut.Structure

namespace HKL41Aux

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem card_filter_add_le (E : Multiset (Finset V)) (p q r s : Finset V → Prop)
    [DecidablePred p] [DecidablePred q] [DecidablePred r] [DecidablePred s]
    (h : ∀ e, (if p e then 1 else 0) + (if q e then 1 else 0) ≤
        (if r e then 1 else 0) + (if s e then (1 : ℕ) else 0)) :
    (E.filter p).card + (E.filter q).card ≤ (E.filter r).card + (E.filter s).card := by
  induction E using Multiset.induction_on with
  | empty => simp
  | cons a E ih =>
    have ha := h a
    simp only [Multiset.filter_cons]
    split_ifs at ha ⊢ <;> simp <;> omega

theorem d_submod (H : HyperKCut.Structure.Hypergraph V) (A B : Finset V) :
    d H (A ∪ B) + d H (A ∩ B) ≤ d H A + d H B := by
  classical
  unfold d
  apply card_filter_add_le
  intro e
  simp only [Meets, Finset.Nonempty, Finset.mem_inter, Finset.mem_union, Finset.mem_compl]
  by_cases h1 : (∃ x, x ∈ e ∧ (x ∈ A ∨ x ∈ B)) ∧ ∃ x, x ∈ e ∧ ¬(x ∈ A ∨ x ∈ B)
  · by_cases h2 : (∃ x, x ∈ e ∧ (x ∈ A ∧ x ∈ B)) ∧ ∃ x, x ∈ e ∧ ¬(x ∈ A ∧ x ∈ B)
    · have hA : (∃ x, x ∈ e ∧ x ∈ A) ∧ ∃ x, x ∈ e ∧ x ∉ A := by
        obtain ⟨⟨x, hx, hxA, -⟩, -⟩ := h2
        obtain ⟨-, ⟨y, hy, hyn⟩⟩ := h1
        exact ⟨⟨x, hx, hxA⟩, ⟨y, hy, fun h => hyn (Or.inl h)⟩⟩
      have hB : (∃ x, x ∈ e ∧ x ∈ B) ∧ ∃ x, x ∈ e ∧ x ∉ B := by
        obtain ⟨⟨x, hx, -, hxB⟩, -⟩ := h2
        obtain ⟨-, ⟨y, hy, hyn⟩⟩ := h1
        exact ⟨⟨x, hx, hxB⟩, ⟨y, hy, fun h => hyn (Or.inr h)⟩⟩
      rw [if_pos h1, if_pos h2, if_pos hA, if_pos hB]
    · have : ((∃ x, x ∈ e ∧ x ∈ A) ∧ ∃ x, x ∈ e ∧ x ∉ A) ∨
          ((∃ x, x ∈ e ∧ x ∈ B) ∧ ∃ x, x ∈ e ∧ x ∉ B) := by
        obtain ⟨⟨x, hx, hxAB⟩, ⟨y, hy, hyn⟩⟩ := h1
        rcases hxAB with hxA | hxB
        · exact Or.inl ⟨⟨x, hx, hxA⟩, ⟨y, hy, fun h => hyn (Or.inl h)⟩⟩
        · exact Or.inr ⟨⟨x, hx, hxB⟩, ⟨y, hy, fun h => hyn (Or.inr h)⟩⟩
      rw [if_pos h1, if_neg h2]
      rcases this with h | h
      · rw [if_pos h]; split_ifs <;> omega
      · rw [if_pos h]; split_ifs <;> omega
  · by_cases h2 : (∃ x, x ∈ e ∧ (x ∈ A ∧ x ∈ B)) ∧ ∃ x, x ∈ e ∧ ¬(x ∈ A ∧ x ∈ B)
    · have : ((∃ x, x ∈ e ∧ x ∈ A) ∧ ∃ x, x ∈ e ∧ x ∉ A) ∨
          ((∃ x, x ∈ e ∧ x ∈ B) ∧ ∃ x, x ∈ e ∧ x ∉ B) := by
        obtain ⟨⟨x, hx, hxA, hxB⟩, ⟨y, hy, hyn⟩⟩ := h2
        by_cases hyA : y ∈ A
        · exact Or.inr ⟨⟨x, hx, hxB⟩, ⟨y, hy, fun h => hyn ⟨hyA, h⟩⟩⟩
        · exact Or.inl ⟨⟨x, hx, hxA⟩, ⟨y, hy, hyA⟩⟩
      rw [if_neg h1, if_pos h2]
      rcases this with h | h
      · rw [if_pos h]; split_ifs <;> omega
      · rw [if_pos h]; split_ifs <;> omega
    · rw [if_neg h1, if_neg h2]; split_ifs <;> omega

/-- The modified partition `(U ∪ V₁, V₂ \ U, …, V_k \ U)` from the proof of Claim 4.1. -/
def modPart {k : ℕ} [NeZero k] (P : Fin k → Finset V) (U : Finset V) : Fin k → Finset V :=
  fun j => if j = 0 then U ∪ P 0 else P j \ U

theorem modPart_partition {k : ℕ} [NeZero k] (P : Fin k → Finset V) (hP : IsPartition P)
    (T U : Finset V) (hUT : Disjoint U T)
    (hTj : ∀ j : Fin k, j ≠ 0 → (T ∩ P j).Nonempty) :
    IsPartition (modPart P U) := by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = 0
    · simp only [modPart, if_pos hj]
      obtain ⟨v, hv⟩ := hP.1 0
      exact ⟨v, Finset.mem_union_right _ hv⟩
    · simp only [modPart, if_neg hj]
      obtain ⟨v, hv⟩ := hTj j hj
      rw [Finset.mem_inter] at hv
      refine ⟨v, Finset.mem_sdiff.mpr ⟨hv.2, fun h => ?_⟩⟩
      exact Finset.disjoint_left.mp hUT h hv.1
  · intro i j hij
    rw [Finset.disjoint_left]
    intro v hvi hvj
    by_cases hi : i = 0
    · have hj : j ≠ 0 := fun h => hij (hi.trans h.symm)
      simp only [modPart, if_pos hi, if_neg hj, Finset.mem_union, Finset.mem_sdiff] at hvi hvj
      rcases hvi with h | h
      · exact hvj.2 h
      · exact Finset.disjoint_left.mp (hP.2.1 0 j (Ne.symm hj)) h hvj.1
    · by_cases hj : j = 0
      · simp only [modPart, if_neg hi, if_pos hj, Finset.mem_union, Finset.mem_sdiff] at hvi hvj
        rcases hvj with h | h
        · exact hvi.2 h
        · exact Finset.disjoint_left.mp (hP.2.1 0 i (Ne.symm hi)) h hvi.1
      · simp only [modPart, if_neg hi, if_neg hj, Finset.mem_sdiff] at hvi hvj
        exact Finset.disjoint_left.mp (hP.2.1 i j hij) hvi.1 hvj.1
  · intro v
    by_cases hvU : v ∈ U
    · exact ⟨0, by simp [modPart, hvU]⟩
    · obtain ⟨i, hi⟩ := hP.2.2 v
      by_cases hi0 : i = 0
      · subst hi0
        exact ⟨0, by simp [modPart, hi]⟩
      · exact ⟨i, by simp [modPart, hi0, hi, hvU]⟩

theorem modPart_cost {k : ℕ} [NeZero k] (H : HyperKCut.Structure.Hypergraph V)
    (P : Fin k → Finset V) (hP : IsPartition P) (U : Finset V) :
    cost H (modPart P U) + d H (P 0) ≤ d H (U ∪ P 0) + cost H P := by
  classical
  unfold cost d
  apply card_filter_add_le
  intro e
  -- facts about a single edge
  have mem0 : ∀ v, v ∈ modPart P U 0 ↔ v ∈ U ∪ P 0 := by
    intro v; simp [modPart]
  have memj : ∀ j : Fin k, j ≠ 0 → ∀ v, v ∈ modPart P U j → v ∈ P j ∧ v ∉ U ∪ P 0 := by
    intro j hj v hv
    simp only [modPart, if_neg hj, Finset.mem_sdiff] at hv
    refine ⟨hv.1, ?_⟩
    rw [Finset.mem_union]
    rintro (h | h)
    · exact hv.2 h
    · exact Finset.disjoint_left.mp (hP.2.1 0 j (Ne.symm hj)) h hv.1
  -- cut of P 0 implies crossing P
  have cutP0 : Meets e (P 0) ∧ Meets e (P 0)ᶜ →
      ∃ i j, i ≠ j ∧ Meets e (P i) ∧ Meets e (P j) := by
    rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    rw [Finset.mem_inter] at hx hy
    obtain ⟨j, hj⟩ := hP.2.2 y
    have hj0 : j ≠ 0 := by
      intro h; subst h; exact (Finset.mem_compl.mp hy.2) hj
    exact ⟨0, j, hj0.symm, ⟨x, Finset.mem_inter.mpr hx⟩, ⟨y, Finset.mem_inter.mpr ⟨hy.1, hj⟩⟩⟩
  -- crossing the modified partition
  have crossW : (∃ i j, i ≠ j ∧ Meets e (modPart P U i) ∧ Meets e (modPart P U j)) →
      ((Meets e (U ∪ P 0) ∧ Meets e (U ∪ P 0)ᶜ) ∨
        ∃ i j, i ≠ j ∧ Meets e (P i) ∧ Meets e (P j)) := by
    rintro ⟨i, j, hij, ⟨x, hx⟩, ⟨y, hy⟩⟩
    rw [Finset.mem_inter] at hx hy
    by_cases hi : i = 0
    · subst hi
      have hj : j ≠ 0 := Ne.symm hij
      have hy' := memj j hj y hy.2
      left
      exact ⟨⟨x, Finset.mem_inter.mpr ⟨hx.1, (mem0 x).mp hx.2⟩⟩,
        ⟨y, Finset.mem_inter.mpr ⟨hy.1, Finset.mem_compl.mpr hy'.2⟩⟩⟩
    · have hx' := memj i hi x hx.2
      by_cases hj : j = 0
      · subst hj
        left
        exact ⟨⟨y, Finset.mem_inter.mpr ⟨hy.1, (mem0 y).mp hy.2⟩⟩,
          ⟨x, Finset.mem_inter.mpr ⟨hx.1, Finset.mem_compl.mpr hx'.2⟩⟩⟩
      · have hy' := memj j hj y hy.2
        by_cases hm : Meets e (U ∪ P 0)
        · left
          exact ⟨hm, ⟨x, Finset.mem_inter.mpr ⟨hx.1, Finset.mem_compl.mpr hx'.2⟩⟩⟩
        · right
          exact ⟨i, j, hij, ⟨x, Finset.mem_inter.mpr ⟨hx.1, hx'.1⟩⟩,
            ⟨y, Finset.mem_inter.mpr ⟨hy.1, hy'.1⟩⟩⟩
  by_cases h1 : ∃ i j, i ≠ j ∧ Meets e (modPart P U i) ∧ Meets e (modPart P U j)
  · by_cases h2 : Meets e (P 0) ∧ Meets e (P 0)ᶜ
    · have h4 := cutP0 h2
      have h3 : Meets e (U ∪ P 0) ∧ Meets e (U ∪ P 0)ᶜ := by
        rcases crossW h1 with h | h
        · exact h
        · -- e meets P 0 ⊆ U ∪ P 0, and crosses W, so it is cut by U ∪ P 0
          obtain ⟨i, j, hij, ⟨x, hx⟩, ⟨y, hy⟩⟩ := h1
          obtain ⟨z, hz⟩ := h2.1
          rw [Finset.mem_inter] at hx hy hz
          refine ⟨⟨z, Finset.mem_inter.mpr ⟨hz.1, Finset.mem_union_right _ hz.2⟩⟩, ?_⟩
          by_cases hi : i = 0
          · subst hi
            have hy' := memj j (Ne.symm hij) y hy.2
            exact ⟨y, Finset.mem_inter.mpr ⟨hy.1, Finset.mem_compl.mpr hy'.2⟩⟩
          · have hx' := memj i hi x hx.2
            exact ⟨x, Finset.mem_inter.mpr ⟨hx.1, Finset.mem_compl.mpr hx'.2⟩⟩
      rw [if_pos h1, if_pos h2, if_pos h3, if_pos h4]
    · rw [if_pos h1, if_neg h2]
      rcases crossW h1 with h | h
      · rw [if_pos h]; split_ifs <;> omega
      · rw [if_pos h]; split_ifs <;> omega
  · by_cases h2 : Meets e (P 0) ∧ Meets e (P 0)ᶜ
    · rw [if_neg h1, if_pos h2, if_pos (cutP0 h2)]; split_ifs <;> omega
    · rw [if_neg h1, if_neg h2]; split_ifs <;> omega

end HKL41Aux

open HKL41Aux in
theorem solution {V : Type} [Fintype V] [DecidableEq V] (H : HyperKCut.Structure.Hypergraph V)
    (k : ℕ) [NeZero k] (hk : 2 ≤ k)
    (P : Fin k → Finset V) (hP : IsMaximalMinKPartition H k P)
    (T : Finset V) (hT : T ⊆ (P 0)ᶜ)
    (hTj : ∀ j : Fin k, j ≠ 0 → (T ∩ P j).Nonempty)
    (S VS : Finset V) (hS : S ⊆ P 0) (hScard : S.card = 2 * k - 2)
    (hVS : IsSourceMaxMinTerminalCut H S T VS)
    (hmax : ∀ (X VX : Finset V), X ⊆ P 0 →
      X.card = 2 * k - 2 →
      IsSourceMaxMinTerminalCut H X T VX → d H VX ≤ d H VS)
    (w : V) (hw : w ∈ P 0 \ VS)
    (u : V) (hu : u ∈ insert w S)
    (B : Finset V)
    (hB : IsSourceMaxMinTerminalCut H ((insert w S).erase u) T B) :
    u ∉ B := by
  rw [Finset.mem_sdiff] at hw
  have hwS : w ∉ S := fun h => hw.2 (hVS.1.1.1 h)
  by_cases huw : u = w
  · subst huw
    have hC : (insert u S).erase u = S := Finset.erase_insert hwS
    rw [hC] at hB
    have hBV : B = VS := Finset.Subset.antisymm (hVS.2 B hB.1) (hB.2 VS hVS.1)
    rw [hBV]
    exact hw.2
  · intro huB
    have huS : u ∈ S := by
      rcases Finset.mem_insert.mp hu with h | h
      · exact absurd h huw
      · exact h
    have hCB : (insert w S).erase u ⊆ B := hB.1.1.1
    have hwB : w ∈ B := hCB (Finset.mem_erase.mpr ⟨Ne.symm huw, Finset.mem_insert_self w S⟩)
    have hSB : S ⊆ B := by
      intro s hs
      by_cases hsu : s = u
      · rw [hsu]; exact huB
      · exact hCB (Finset.mem_erase.mpr ⟨hsu, Finset.mem_insert_of_mem hs⟩)
    -- d(B) ≤ d(V_S) by the choice of S
    have hCP : (insert w S).erase u ⊆ P 0 := by
      intro x hx
      rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase hx) with h | h
      · rw [h]; exact hw.1
      · exact hS h
    have hCcard : ((insert w S).erase u).card = 2 * k - 2 := by
      rw [Finset.card_erase_of_mem hu, Finset.card_insert_of_notMem hwS, hScard]
      omega
    have hBle := hmax _ B hCP hCcard hB
    -- uncrossing
    have hint : d H VS ≤ d H (VS ∩ B) :=
      hVS.1.2 _ ⟨Finset.subset_inter hVS.1.1.1 hSB,
        Disjoint.mono_left Finset.inter_subset_left hVS.1.1.2⟩
    have huni_t : IsTerminalCut S T (VS ∪ B) :=
      ⟨hVS.1.1.1.trans Finset.subset_union_left,
        Finset.disjoint_union_left.mpr ⟨hVS.1.1.2, hB.1.1.2⟩⟩
    have hsm := d_submod H VS B
    have hmin : IsMinTerminalCut H S T (VS ∪ B) := by
      refine ⟨huni_t, fun U' hU' => ?_⟩
      have := hVS.1.2 U' hU'
      omega
    have := hVS.2 _ hmin
    exact hw.2 (this (Finset.mem_union_right _ hwB))
