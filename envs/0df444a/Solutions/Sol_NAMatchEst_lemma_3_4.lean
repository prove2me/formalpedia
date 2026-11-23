-- Prove2me | solution 1 for NAMatchEst.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:33:17.606819+00:00
-- url     : https://prove2.me/submissions/f194014f-c682-45af-b980-d30090c5a3b1

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_V1
import Definitions.Def_NAMatchEst_RH
import Definitions.Def_NAMatchEst_W3




namespace NAMatchEst.AuxL34

open SimpleGraph

theorem bdd {V : Type*} [Fintype V] (G : SimpleGraph V) :
    BddAbove {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m} := by
  refine ⟨Nat.card (Sym2 V), ?_⟩
  rintro m ⟨M, -, rfl⟩
  exact Set.ncard_le_card _

theorem exists_max {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = TuranMatching.Clique.matchingNumber G :=
  Nat.sSup_mem (s := {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m})
    ⟨0, ⊥, fun v hv => by simp at hv, by simp⟩ (bdd G)

/-- In a matching, the number of edges meeting a set `B` is at most `|B|`. -/
theorem card_bad_le {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {M : G.Subgraph} (hM : M.IsMatching) (B : Finset V) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, e ∈ M.edgeSet) :
    (E.filter (fun e => ¬ ∀ v ∈ e, v ∉ B)).card ≤ B.card := by
  classical
  let p : V → V := fun v => if h : v ∈ M.verts then (hM h).choose else v
  have hpu : ∀ v w, M.Adj v w → p v = w := fun v w h => by
    have hv := h.fst_mem
    simp only [p, dif_pos hv]
    exact ((hM hv).choose_spec.2 w h).symm
  refine le_trans (Finset.card_le_card ?_) (Finset.card_image_le (s := B) (f := fun v => s(v, p v)))
  intro e he
  induction e using Sym2.ind with
  | h a b =>
    simp only [Finset.mem_filter] at he
    obtain ⟨hab, hB⟩ := he
    have hab : M.Adj a b := hE _ hab
    push Not at hB
    obtain ⟨v, hv, hvB⟩ := hB
    simp only [Finset.mem_image]
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ⟨v, hvB, by rw [hpu _ _ hab]⟩
    · exact ⟨v, hvB, by rw [hpu _ _ hab.symm, Sym2.eq_swap]⟩

end NAMatchEst.AuxL34

open NAMatchEst NAMatchEst.AuxL34 SimpleGraph in
theorem solution (n : ℕ) (α : ℝ) (k : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n → α ^ 2 < k →
    ∀ (G : AdjList n) (H : Finset (Fin n)), k ≤ TuranMatching.Clique.matchingNumber G.toGraph → H ⊆ V1 G α k →
      (k : ℝ) / 8 ≤ (V1 G α k).card ∨ (k : ℝ) * α / 4 ≤ RH G α k H ∨
        ∃ M : G.toGraph.Subgraph, M.IsMatching ∧ M.verts ⊆ ↑(W3 G α k H) ∧
          (k : ℝ) / 2 ≤ M.edgeSet.ncard := by
  classical
  intro h13 h12 hαk hkn hα2 G H hkμ hHV1
  by_contra hcon
  push Not at hcon
  obtain ⟨hV1, hRH, hno⟩ := hcon
  have hkpos : (0 : ℝ) < k := lt_of_le_of_lt (sq_nonneg α) hα2
  have hk1 : (1 : ℝ) ≤ k := by
    have : 0 < k := by exact_mod_cast hkpos
    exact_mod_cast this
  have hn : (1 : ℝ) ≤ n := le_trans hk1 hkn
  have hα : 0 < α := lt_of_lt_of_le one_pos (le_trans (Real.one_le_rpow hn (by norm_num)) h13)
  obtain ⟨M, hM, hμ⟩ := exists_max G.toGraph
  set W := W3 G α k H with hW
  -- the submatching
  let s : Set (Fin n) := {v | v ∈ W ∧ ∃ w, w ∈ W ∧ M.Adj v w}
  let M' := M.induce s
  have hM' : M'.IsMatching := by
    intro v hv
    obtain ⟨hvW, w, hwW, hvw⟩ := hv
    refine ⟨w, ⟨⟨hvW, w, hwW, hvw⟩, ⟨hwW, v, hvW, hvw.symm⟩, hvw⟩, ?_⟩
    intro y hy
    obtain ⟨-, -, hy⟩ := hy
    obtain ⟨z, -, hz⟩ := hM hvw.fst_mem
    rw [hz y hy, hz w hvw]
  have hM'verts : M'.verts ⊆ ↑W := fun v hv => hv.1
  have hlast := hno M' hM' hM'verts
  -- counting
  set E := M.edgeSet.toFinset with hE
  have hEcard : (k : ℝ) ≤ E.card := by
    rw [hE, ← Set.ncard_eq_toFinset_card' M.edgeSet, hμ]; exact_mod_cast hkμ
  let B : Finset (Fin n) := Finset.univ \ W
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := E) (fun e : Sym2 (Fin n) => ∀ v ∈ e, v ∉ B)
  have hbad := card_bad_le hM B E (fun e he => by simpa [hE] using he)
  have hgood : (E.filter (fun e : Sym2 (Fin n) => ∀ v ∈ e, v ∉ B)).card ≤ M'.edgeSet.ncard := by
    rw [Set.ncard_eq_toFinset_card' M'.edgeSet]
    apply Finset.card_le_card
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      simp only [hE, Finset.mem_filter, Set.mem_toFinset, Subgraph.mem_edgeSet] at he ⊢
      obtain ⟨hab, hgd⟩ := he
      have ha : a ∈ W := by
        have := hgd a (Sym2.mem_mk_left a b); simpa [B] using this
      have hb : b ∈ W := by
        have := hgd b (Sym2.mem_mk_right a b); simpa [B] using this
      exact ⟨⟨ha, b, hb, hab⟩, ⟨hb, a, ha, hab.symm⟩, hab⟩
  -- size of B
  have hBsub : B ⊆ V1 G α k ∪ (U G α k \ W) := by
    intro v hv
    have hvW : v ∉ W := by simpa [B] using hv
    by_cases hv1 : v ∈ V1 G α k
    · exact Finset.mem_union_left _ hv1
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨by simp [U, hv1], hvW⟩)
  have hBcard : (B.card : ℝ) ≤ (V1 G α k).card + (U G α k \ W).card := by
    exact_mod_cast (Finset.card_le_card hBsub).trans (Finset.card_union_le _ _)
  have hUW : ((U G α k \ W).card : ℝ) * α ≤ RH G α k H := by
    have h1 : ((U G α k \ W).card : ℝ) * α ≤ ∑ u ∈ U G α k \ W, (dHbar G H u : ℝ) := by
      rw [← nsmul_eq_mul]
      refine Finset.card_nsmul_le_sum _ _ _ fun u hu => ?_
      obtain ⟨huU, huW⟩ := Finset.mem_sdiff.1 hu
      by_contra hlt
      push Not at hlt
      exact huW (by simp [hW, W3, huU, hlt])
    have h2 : ∑ u ∈ U G α k \ W, (dHbar G H u : ℝ) ≤ ∑ u ∈ U G α k, (dHbar G H u : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset (fun _ _ _ => Nat.cast_nonneg _)
    rw [RH, Nat.cast_sum]
    linarith
  have hUW' : ((U G α k \ W).card : ℝ) < k / 4 := by
    by_contra h
    push Not at h
    have := mul_le_mul_of_nonneg_right h hα.le
    linarith
  have hsplit' : ((E.filter (fun e : Sym2 (Fin n) => ∀ v ∈ e, v ∉ B)).card : ℝ) +
      (E.filter (fun e : Sym2 (Fin n) => ¬ ∀ v ∈ e, v ∉ B)).card = E.card := by
    exact_mod_cast hsplit
  have hbad' : ((E.filter (fun e : Sym2 (Fin n) => ¬ ∀ v ∈ e, v ∉ B)).card : ℝ) ≤ B.card := by
    norm_cast; convert hbad
  have hgood' : ((E.filter (fun e : Sym2 (Fin n) => ∀ v ∈ e, v ∉ B)).card : ℝ) ≤
      M'.edgeSet.ncard := by exact_mod_cast hgood
  linarith
