-- Prove2me | solution 1 for NAMatchEst.observation_3_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:33:15.397585+00:00
-- url     : https://prove2.me/submissions/e68ce2d5-0157-43e2-a25b-101ed52ea8dc

import Mathlib
import Definitions.Def_TuranMatching_Clique_Setting
import Definitions.Def_NAMatchEst_AdjList
import Definitions.Def_NAMatchEst_AdjList_toGraph
import Definitions.Def_NAMatchEst_C0
import Definitions.Def_NAMatchEst_V1




namespace NAMatchEst.AuxObs32

open SimpleGraph

theorem bdd {V : Type*} [Fintype V] (G : SimpleGraph V) :
    BddAbove {m | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = m} := by
  refine ⟨Nat.card (Sym2 V), ?_⟩
  rintro m ⟨M, -, rfl⟩
  exact Set.ncard_le_card _

theorem le_mn {V : Type*} [Fintype V] {G : SimpleGraph V} {M : G.Subgraph} (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ TuranMatching.Clique.matchingNumber G :=
  le_csSup (bdd G) ⟨M, hM, rfl⟩

theorem card_verts {V : Type*} [Fintype V] {G : SimpleGraph V} {M : G.Subgraph}
    (hM : M.IsMatching) : M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  let p : V → V := fun v => if h : v ∈ M.verts then (hM h).choose else v
  have hp : ∀ v ∈ M.verts, M.Adj v (p v) := fun v hv => by
    simp only [p, dif_pos hv]; exact (hM hv).choose_spec.1
  have hpu : ∀ v w, M.Adj v w → p v = w := fun v w h => by
    have hv := h.fst_mem
    simp only [p, dif_pos hv]
    exact ((hM hv).choose_spec.2 w h).symm
  rw [Set.ncard_eq_toFinset_card' M.verts, Set.ncard_eq_toFinset_card' M.edgeSet]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun v => s(v, p v)) (t := M.edgeSet.toFinset)]
  · rw [Finset.sum_const_nat (m := 2)]
    · ring
    intro e he
    induction e using Sym2.ind with
    | h a b =>
      have hab : M.Adj a b := by simpa using he
      have : {x ∈ M.verts.toFinset | s(x, p x) = s(a, b)} = {a, b} := by
        ext v
        simp only [Finset.mem_filter, Set.mem_toFinset, Finset.mem_insert,
          Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩
          rcases Sym2.eq_iff.1 h with h | h
          · exact Or.inl h.1
          · exact Or.inr h.1
        · rintro (rfl | rfl)
          · exact ⟨hab.fst_mem, by rw [hpu _ _ hab]⟩
          · exact ⟨hab.snd_mem, by rw [hpu _ _ hab.symm, Sym2.eq_swap]⟩
      rw [this, Finset.card_pair hab.ne]
  · intro v hv
    simp only [Finset.mem_coe, Set.mem_toFinset] at hv ⊢
    exact hp v hv

end NAMatchEst.AuxObs32

open NAMatchEst NAMatchEst.AuxObs32 SimpleGraph in
theorem solution (n : ℕ) (α : ℝ) (k : ℕ) :
    (n : ℝ) ^ ((1 : ℝ) / 3) ≤ α → α ≤ (n : ℝ) ^ ((1 : ℝ) / 2) → α ≤ k → (k : ℝ) ≤ n →
    ∀ (G : AdjList n) (M : G.toGraph.Subgraph), M.IsMatching →
      M.edgeSet.ncard = TuranMatching.Clique.matchingNumber G.toGraph →
      (∀ u v, G.toGraph.Adj u v → u ∈ M.verts ∨ v ∈ M.verts) ∧
      M.verts.ncard = 2 * TuranMatching.Clique.matchingNumber G.toGraph ∧
      ((TuranMatching.Clique.matchingNumber G.toGraph : ℝ) < k / (C0 * α) →
        (↑(V1 G α k) : Set (Fin n)) ⊆ M.verts ∧ ((V1 G α k).card : ℝ) < 2 * k / (C0 * α) ∧
          2 * (k : ℝ) / (C0 * α) ≤ k / 100) ∧
      ∀ (S : Finset (Fin n)) (D : ℝ), 0 ≤ D → (∀ v ∈ S, (((G.adj v).toFinset ∩ S).card : ℝ) ≤ D) →
        (({e ∈ G.toGraph.edgeSet | ∀ v ∈ e, v ∈ S}.ncard : ℕ) : ℝ) ≤ D * M.verts.ncard := by
  classical
  intro h13 h12 hαk hkn G M hM hμ
  set μ := TuranMatching.Clique.matchingNumber G.toGraph with hμdef
  -- (a) cover
  have hcover : ∀ u v, G.toGraph.Adj u v → u ∈ M.verts ∨ v ∈ M.verts := by
    intro u v huv
    by_contra hcon
    push Not at hcon
    obtain ⟨hu, hv⟩ := hcon
    have hM' : (M ⊔ G.toGraph.subgraphOfAdj huv).IsMatching := by
      refine hM.sup (Subgraph.IsMatching.subgraphOfAdj huv) ?_
      rw [hM.support_eq_verts]
      refine Set.disjoint_left.2 fun x hx hx' => ?_
      have := (G.toGraph.subgraphOfAdj huv).support_subset_verts hx'
      simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at this
      rcases this with rfl | rfl
      · exact hu hx
      · exact hv hx
    have hle := le_mn hM'
    rw [Subgraph.edgeSet_sup, edgeSet_subgraphOfAdj, Set.union_singleton,
      Set.ncard_insert_of_notMem] at hle
    · omega
    · intro hmem
      exact hu (M.mem_verts_of_mem_edge hmem (Sym2.mem_mk_left u v))
  have hcard : M.verts.ncard = 2 * μ := by rw [card_verts hM, hμ]
  refine ⟨hcover, hcard, ?_, ?_⟩
  · -- (c)
    intro hlt
    have hα : 0 < α := by
      by_contra h
      push Not at h
      have : (k : ℝ) / (C0 * α) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _)
          (mul_nonpos_of_nonneg_of_nonpos (by norm_num [C0]) h)
      have : (0 : ℝ) ≤ μ := Nat.cast_nonneg _
      linarith
    have hk : (1 : ℝ) ≤ k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        have : (0 : ℝ) ≤ μ := Nat.cast_nonneg _
        simp at hlt
        linarith
      · exact_mod_cast h
    have hn : (1 : ℝ) ≤ n := le_trans hk hkn
    have hα1 : 1 ≤ α := le_trans (Real.one_le_rpow hn (by norm_num)) h13
    have hC0 : C0 = 2 ^ 20 := rfl
    have hC0pos : (0 : ℝ) < C0 := by rw [hC0]; norm_num
    have hsub : (↑(V1 G α k) : Set (Fin n)) ⊆ M.verts := by
      intro v hv
      by_contra hvM
      have hsubC : (G.adj v).toFinset ⊆ M.verts.toFinset := by
        intro w hw
        rw [List.mem_toFinset] at hw
        rcases hcover v w hw with h | h
        · exact absurd h hvM
        · simpa using h
      have hlen : (G.adj v).length ≤ 2 * μ := by
        rw [← List.toFinset_card_of_nodup (G.nodup v), ← hcard,
          Set.ncard_eq_toFinset_card' M.verts]
        exact Finset.card_le_card hsubC
      have hD : Delta k α ≤ (G.adj v).length := by
        simpa [V1] using hv
      have hfl := Nat.sub_one_lt_floor (2 * (k : ℝ) / α)
      have hx : 2 ≤ 2 * (k : ℝ) / α := by
        rw [le_div_iff₀ hα]; linarith
      have h1 : 2 * (k : ℝ) / (C0 * α) = (2 * (k : ℝ) / α) / C0 := by
        rw [div_div, mul_comm C0]
      have h2 : (2 * (k : ℝ) / α) / C0 ≤ (2 * (k : ℝ) / α) / 2 :=
        div_le_div_of_nonneg_left (by linarith) (by norm_num) (by rw [hC0]; norm_num)
      have hDr : ((Delta k α : ℕ) : ℝ) ≤ (G.adj v).length := by exact_mod_cast hD
      have hlr : ((G.adj v).length : ℝ) ≤ 2 * μ := by exact_mod_cast hlen
      unfold Delta at hDr
      have : 2 * (μ : ℝ) < 2 * k / (C0 * α) := by
        have := mul_lt_mul_of_pos_left hlt (by norm_num : (0:ℝ) < 2)
        rw [mul_div_assoc]; exact this
      linarith
    refine ⟨hsub, ?_, ?_⟩
    · have hle : (V1 G α k).card ≤ 2 * μ := by
        rw [← hcard, Set.ncard_eq_toFinset_card' M.verts]
        apply Finset.card_le_card
        intro v hv
        simpa using hsub (Finset.mem_coe.2 hv)
      have hle' : ((V1 G α k).card : ℝ) ≤ 2 * μ := by exact_mod_cast hle
      have : 2 * (μ : ℝ) < 2 * k / (C0 * α) := by
        have := mul_lt_mul_of_pos_left hlt (by norm_num : (0:ℝ) < 2)
        rw [mul_div_assoc]; exact this
      linarith
    · rw [div_le_div_iff₀ (mul_pos hC0pos hα) (by norm_num)]
      have : (200 : ℝ) ≤ C0 * α := by rw [hC0]; nlinarith
      nlinarith
  · -- (d)
    intro S D hD hdeg
    set C := M.verts.toFinset with hC
    let T : Finset (Sym2 (Fin n)) :=
      (C ∩ S).biUnion (fun w => ((G.adj w).toFinset ∩ S).image (fun x => s(w, x)))
    have hsubT : {e ∈ G.toGraph.edgeSet | ∀ v ∈ e, v ∈ S} ⊆ (T : Set (Sym2 (Fin n))) := by
      intro e he
      induction e using Sym2.ind with
      | h a b =>
        obtain ⟨hab, hS⟩ := he
        have hab' : G.toGraph.Adj a b := hab
        have haS : a ∈ S := hS a (Sym2.mem_mk_left a b)
        have hbS : b ∈ S := hS b (Sym2.mem_mk_right a b)
        simp only [T, Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Finset.mem_inter,
          Finset.mem_image, List.mem_toFinset]
        rcases hcover a b hab' with h | h
        · exact ⟨a, ⟨by simpa [hC] using h, haS⟩, b, ⟨hab', hbS⟩, rfl⟩
        · exact ⟨b, ⟨by simpa [hC] using h, hbS⟩, a, ⟨hab'.symm, haS⟩, Sym2.eq_swap⟩
    have h1 : {e ∈ G.toGraph.edgeSet | ∀ v ∈ e, v ∈ S}.ncard ≤ T.card := by
      rw [← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard hsubT
    have h2 : T.card ≤ ∑ w ∈ C ∩ S, ((G.adj w).toFinset ∩ S).card :=
      Finset.card_biUnion_le.trans (Finset.sum_le_sum fun w _ => Finset.card_image_le)
    have h3 : (∑ w ∈ C ∩ S, (((G.adj w).toFinset ∩ S).card : ℝ)) ≤ ∑ w ∈ C ∩ S, D :=
      Finset.sum_le_sum fun w hw => hdeg w (Finset.mem_inter.1 hw).2
    have h4 : ((C ∩ S).card : ℝ) ≤ C.card := by
      exact_mod_cast Finset.card_le_card Finset.inter_subset_left
    have h12 : (({e ∈ G.toGraph.edgeSet | ∀ v ∈ e, v ∈ S}.ncard : ℕ) : ℝ) ≤
        ∑ w ∈ C ∩ S, (((G.adj w).toFinset ∩ S).card : ℝ) := by
      rw [← Nat.cast_sum]; exact_mod_cast h1.trans h2
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    rw [Set.ncard_eq_toFinset_card' M.verts, ← hC]
    nlinarith
