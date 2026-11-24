-- Prove2me | solution 1 for HindsightGain.Uniform.Supplement.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T18:08:03.073805+00:00
-- url     : https://prove2.me/submissions/79fd40e4-6d25-4761-9a16-30c16ee742ea

import Mathlib
import Definitions.Def_HindsightGain_Uniform_Supplement_planted

set_option autoImplicit false
open Classical

namespace HGA3Aux

open HindsightGain.Uniform.Supplement Finset

/-! ### Frobenius-norm bound on closed-walk counts -/

/-- The squared Frobenius norm. -/
noncomputable def fro {V : Type} [Fintype V] (X : Matrix V V ℝ) : ℝ := ∑ i, ∑ j, X i j ^ 2

theorem fro_nonneg {V : Type} [Fintype V] (X : Matrix V V ℝ) : 0 ≤ fro X :=
  sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))

theorem fro_mul {V : Type} [Fintype V] (X Y : Matrix V V ℝ) : fro (X * Y) ≤ fro X * fro Y := by
  unfold fro
  calc ∑ i, ∑ j, (X * Y) i j ^ 2 ≤ ∑ i, ∑ j, (∑ k, X i k ^ 2) * (∑ k, Y k j ^ 2) := by
        apply sum_le_sum; intro i _; apply sum_le_sum; intro j _
        rw [Matrix.mul_apply]
        exact sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, ∑ k, X i k ^ 2) * ∑ j, ∑ k, Y k j ^ 2 := by rw [sum_mul_sum]
    _ = (∑ i, ∑ k, X i k ^ 2) * ∑ i, ∑ j, Y i j ^ 2 := by congr 1; exact sum_comm

theorem trace_mul_sq {V : Type} [Fintype V] (X Y : Matrix V V ℝ) :
    (Matrix.trace (X * Y)) ^ 2 ≤ fro X * fro Y := by
  unfold fro
  have h1 : Matrix.trace (X * Y) = ∑ p : V × V, X p.1 p.2 * Y p.2 p.1 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    rw [← univ_product_univ, sum_product]
  rw [h1]
  calc (∑ p : V × V, X p.1 p.2 * Y p.2 p.1) ^ 2
      ≤ (∑ p : V × V, X p.1 p.2 ^ 2) * ∑ p : V × V, Y p.2 p.1 ^ 2 :=
        sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, ∑ j, X i j ^ 2) * ∑ i, ∑ j, Y i j ^ 2 := by
        rw [← univ_product_univ, sum_product, sum_product]
        congr 1
        exact sum_comm

theorem fro_pow {V : Type} [Fintype V] (X : Matrix V V ℝ) :
    ∀ m : ℕ, 1 ≤ m → fro (X ^ m) ≤ fro X ^ m := by
  intro m hm
  induction m with
  | zero => exact absurd hm (by norm_num)
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · subst h0; simp
    · rw [pow_succ, pow_succ]
      calc fro (X ^ m * X) ≤ fro (X ^ m) * fro X := fro_mul _ _
        _ ≤ fro X ^ m * fro X := mul_le_mul_of_nonneg_right (ih hpos) (fro_nonneg X)

theorem fro_adj {V : Type} [Fintype V] (G : SimpleGraph V) :
    fro (G.adjMatrix ℝ) = 2 * (G.edgeFinset.card : ℝ) := by
  unfold fro
  have hsq : ∀ i j, (G.adjMatrix ℝ i j) ^ 2 = if G.Adj i j then (1 : ℝ) else 0 := by
    intro i j
    rw [SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  simp only [hsq, sum_boole]
  have hd : ∀ i, ((univ.filter (fun j => G.Adj i j)).card) = G.degree i := fun i => by
    rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  simp only [hd]
  exact_mod_cast G.sum_degrees_eq_twice_card_edges

theorem trace_nonneg_pow {V : Type} [Fintype V] (G : SimpleGraph V) (L : ℕ) :
    0 ≤ Matrix.trace (G.adjMatrix ℝ ^ L) := by
  simp only [Matrix.trace, Matrix.diag_apply, SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
  exact sum_nonneg (fun _ _ => Nat.cast_nonneg _)

theorem trace_le {V : Type} [Fintype V] (G : SimpleGraph V) (L : ℕ) (hL : 1 ≤ L) :
    Matrix.trace (G.adjMatrix ℝ ^ L) ≤ Real.sqrt (2 * (G.edgeFinset.card : ℝ)) ^ L := by
  obtain ⟨m, rfl⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  rcases Nat.eq_zero_or_pos m with h0 | hm
  · subst h0
    have : Matrix.trace (G.adjMatrix ℝ ^ (0 + 1)) = 0 := by
      simp [Matrix.trace, SimpleGraph.adjMatrix_apply]
    rw [this]
    exact pow_nonneg (Real.sqrt_nonneg _) _
  · have h := trace_mul_sq (G.adjMatrix ℝ) (G.adjMatrix ℝ ^ m)
    have h2 := fro_pow (G.adjMatrix ℝ) m hm
    rw [← pow_succ'] at h
    have hf := fro_adj G
    have hs : Real.sqrt (2 * (G.edgeFinset.card : ℝ)) ^ 2 = 2 * (G.edgeFinset.card : ℝ) :=
      Real.sq_sqrt (by positivity)
    apply le_of_pow_le_pow_left₀ (n := 2) two_ne_zero (pow_nonneg (Real.sqrt_nonneg _) _)
    calc Matrix.trace (G.adjMatrix ℝ ^ (m + 1)) ^ 2
        ≤ fro (G.adjMatrix ℝ) * fro (G.adjMatrix ℝ ^ m) := h
      _ ≤ fro (G.adjMatrix ℝ) * fro (G.adjMatrix ℝ) ^ m :=
          mul_le_mul_of_nonneg_left h2 (fro_nonneg _)
      _ = (Real.sqrt (2 * (G.edgeFinset.card : ℝ)) ^ 2) ^ (m + 1) := by
          rw [hs, hf, pow_succ]; ring
      _ = (Real.sqrt (2 * (G.edgeFinset.card : ℝ)) ^ (m + 1)) ^ 2 := by
          ring

/-! ### Edge sets of closed walks -/

/-- Edge sets of closed walks of length `L`. -/
noncomputable def closedEdgeSets {V : Type} [Fintype V] (G : SimpleGraph V) (L : ℕ) :
    Finset (Finset (Sym2 V)) :=
  (univ : Finset (Σ v : V, ({p : G.Walk v v | p.length = L} : Set (G.Walk v v)))).image
    (fun x => x.2.1.edges.toFinset)

theorem card_closedEdgeSets_le {V : Type} [Fintype V] (G : SimpleGraph V) (L : ℕ) :
    ((closedEdgeSets G L).card : ℝ) ≤ Matrix.trace (G.adjMatrix ℝ ^ L) := by
  unfold closedEdgeSets
  calc ((univ.image _).card : ℝ)
      ≤ ((univ : Finset (Σ v : V, ({p : G.Walk v v | p.length = L} : Set (G.Walk v v)))).card :
          ℝ) := by exact_mod_cast card_image_le
    _ = Matrix.trace (G.adjMatrix ℝ ^ L) := by
        rw [card_univ, Fintype.card_sigma]
        simp only [Matrix.trace, Matrix.diag_apply, SimpleGraph.adjMatrix_pow_apply_eq_card_walk]
        push_cast
        rfl

/-! ### Even edge sets -/

theorem even_sdiff {V : Type} {J C : Finset (Sym2 V)} (hC : C ⊆ J) (hJ : IsEvenEdgeSet J)
    (hCe : IsEvenEdgeSet C) : IsEvenEdgeSet (J \ C) := by
  intro v
  have hu : (J.filter (fun z => v ∈ z)).card =
      ((J \ C).filter (fun z => v ∈ z)).card + (C.filter (fun z => v ∈ z)).card := by
    rw [← card_union_of_disjoint (disjoint_filter_filter sdiff_disjoint), ← filter_union,
      sdiff_union_of_subset hC]
  have h1 := hJ v
  rw [hu] at h1
  exact (Nat.even_add.mp h1).mpr (hCe v)

theorem even_trail {V : Type} {G : SimpleGraph V} {v : V} (p : G.Walk v v) (ht : p.IsTrail) :
    IsEvenEdgeSet p.edges.toFinset := by
  intro x
  have h := (ht.even_countP_edges_iff x).mpr (fun h => absurd rfl h)
  have hc : (p.edges.toFinset.filter (fun z => x ∈ z)).card =
      p.edges.countP (fun z => x ∈ z) := by
    rw [List.countP_eq_length_filter,
      ← List.toFinset_card_of_nodup (ht.edges_nodup.filter _)]
    congr 1
    ext e
    simp
  rw [hc]
  exact h

theorem exists_trail {V : Type} [Fintype V] (G : SimpleGraph V) (J : Finset (Sym2 V))
    (hJ : J ⊆ edgeFinset' G) (hne : J.Nonempty) (hev : IsEvenEdgeSet J) :
    ∃ (v : V) (p : G.Walk v v), p.IsTrail ∧ 3 ≤ p.length ∧ p.edges.toFinset ⊆ J := by
  have hJG : ∀ e ∈ J, e ∈ G.edgeSet := fun e he => by
    have := hJ he
    simp only [edgeFinset', mem_filter, mem_univ, true_and] at this
    exact this
  let H := SimpleGraph.fromEdgeSet (J : Set (Sym2 V))
  have hHadj : ∀ a b, H.Adj a b ↔ s(a, b) ∈ J ∧ a ≠ b := by
    intro a b; simp [H, SimpleGraph.fromEdgeSet_adj]
  have hle : H ≤ G := by
    intro a b h
    exact hJG _ ((hHadj a b).mp h).1
  by_cases hac : H.IsAcyclic
  · exfalso
    obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | h a b =>
    have hab : a ≠ b := (hJG _ he).ne
    have hHab : H.Adj a b := (hHadj a b).mpr ⟨he, hab⟩
    have : Nonempty V := ⟨a⟩
    obtain ⟨u, v, p, hp, hmax⟩ := SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length H
    have hlen : 1 ≤ p.length := by
      have := hmax a b (SimpleGraph.Path.singleton hHab).1 (SimpleGraph.Path.singleton hHab).2
      simpa using this
    have hnil : ¬ p.Nil := by
      rw [SimpleGraph.Walk.nil_iff_length_eq]; omega
    have huniq : ∀ w, H.Adj u w → w = p.snd := by
      intro w hadj
      apply hac.eq_snd_of_adj_start hp hadj
      by_contra hw
      have hp' : (SimpleGraph.Walk.cons hadj.symm p).IsPath := hp.cons hw
      have := hmax _ _ _ hp'
      simp at this
    have hfil : J.filter (fun z => u ∈ z) = {s(u, p.snd)} := by
      ext z
      simp only [mem_filter, mem_singleton]
      constructor
      · rintro ⟨hz, huz⟩
        obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp huz
        have hne' : u ≠ w := (hJG _ hz).ne
        rw [huniq w ((hHadj u w).mpr ⟨hz, hne'⟩)]
      · rintro rfl
        exact ⟨((hHadj u p.snd).mp (p.adj_snd hnil)).1, Sym2.mem_mk_left _ _⟩
    have h := hev u
    rw [hfil, card_singleton] at h
    exact Nat.not_even_one h
  · simp only [SimpleGraph.IsAcyclic, not_forall, not_not] at hac
    obtain ⟨v, c, hc⟩ := hac
    refine ⟨v, c.mapLe hle, (SimpleGraph.Walk.isTrail_mapLe hle).mpr hc.isCircuit.isTrail,
      by rw [SimpleGraph.Walk.length_mapLe]; exact hc.three_le_length, ?_⟩
    rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
    intro e he
    rw [List.mem_toFinset] at he
    have := c.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_fromEdgeSet] at this
    exact mem_coe.mp this.1

/-- The even edge sets of `G` with exactly `k` edges. -/
noncomputable def evenSets {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    Finset (Finset (Sym2 V)) :=
  (edgeFinset' G).powerset.filter (fun J => IsEvenEdgeSet J ∧ J.card = k)

theorem evenSets_rec {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) (hk : 1 ≤ k) :
    ((evenSets G k).card : ℝ) ≤
      ∑ i ∈ range k, ((closedEdgeSets G (i + 1)).card : ℝ) *
        ((evenSets G (k - (i + 1))).card : ℝ) := by
  have hsub : evenSets G k ⊆ (range k).biUnion (fun i =>
      ((closedEdgeSets G (i + 1)) ×ˢ (evenSets G (k - (i + 1)))).image (fun x => x.1 ∪ x.2)) := by
    intro J hJ
    simp only [evenSets, mem_filter, mem_powerset] at hJ
    obtain ⟨hJE, hJev, hJk⟩ := hJ
    have hne : J.Nonempty := by
      rw [← card_pos]; omega
    obtain ⟨v, p, ht, h3, hpJ⟩ := exists_trail G J hJE hne hJev
    have hcard : p.edges.toFinset.card = p.length := by
      rw [List.toFinset_card_of_nodup ht.edges_nodup, SimpleGraph.Walk.length_edges]
    have hLk : p.length ≤ k := by rw [← hcard, ← hJk]; exact card_le_card hpJ
    rw [mem_biUnion]
    refine ⟨p.length - 1, mem_range.mpr (by omega), ?_⟩
    rw [mem_image]
    refine ⟨(p.edges.toFinset, J \ p.edges.toFinset), ?_, ?_⟩
    · rw [mem_product]
      constructor
      · unfold closedEdgeSets
        rw [mem_image]
        exact ⟨⟨v, ⟨p, by simp only [Set.mem_setOf_eq]; omega⟩⟩, mem_univ _, rfl⟩
      · simp only [evenSets, mem_filter, mem_powerset]
        refine ⟨sdiff_subset.trans hJE, even_sdiff hpJ hJev (even_trail p ht), ?_⟩
        rw [card_sdiff_of_subset hpJ, hcard, hJk]
        omega
    · exact union_sdiff_of_subset hpJ
  calc ((evenSets G k).card : ℝ)
      ≤ (((range k).biUnion (fun i =>
          ((closedEdgeSets G (i + 1)) ×ˢ (evenSets G (k - (i + 1)))).image
            (fun x => x.1 ∪ x.2))).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ ((∑ i ∈ range k, (((closedEdgeSets G (i + 1)) ×ˢ (evenSets G (k - (i + 1)))).image
            (fun x => x.1 ∪ x.2)).card : ℕ) : ℝ) := by exact_mod_cast card_biUnion_le
    _ ≤ ((∑ i ∈ range k, ((closedEdgeSets G (i + 1)).card *
            (evenSets G (k - (i + 1))).card) : ℕ) : ℝ) := by
        exact_mod_cast sum_le_sum (fun i _ => (card_image_le).trans (card_product _ _).le)
    _ = _ := by push_cast; rfl

theorem numeric (N a : ℕ → ℝ) (s : ℝ) (hs : 0 ≤ s) (hN0 : N 0 ≤ 1) (hNnn : ∀ k, 0 ≤ N k)
    (ha : ∀ i, a (i + 1) ≤ s ^ (i + 1)) (ha0 : ∀ i, 0 ≤ a i)
    (hrec : ∀ k, 1 ≤ k → N k ≤ ∑ i ∈ range k, a (i + 1) * N (k - (i + 1))) :
    ∀ k, N k ≤ 2 ^ k * s ^ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with h0 | hk
    · subst h0; simpa using hN0
    calc N k ≤ ∑ i ∈ range k, a (i + 1) * N (k - (i + 1)) := hrec k hk
      _ ≤ ∑ i ∈ range k, s ^ (i + 1) * (2 ^ (k - (i + 1)) * s ^ (k - (i + 1))) := by
          apply sum_le_sum
          intro i hi
          have hi' := mem_range.mp hi
          exact mul_le_mul (ha i) (ih _ (by omega)) (hNnn _) (pow_nonneg hs _)
      _ = ∑ i ∈ range k, (2 : ℝ) ^ (k - 1 - i) * s ^ k := by
          apply sum_congr rfl
          intro i hi
          have hi' := mem_range.mp hi
          have e1 : k - (i + 1) = k - 1 - i := by omega
          have e2 : s ^ (i + 1) * s ^ (k - 1 - i) = s ^ k := by
            rw [← pow_add]; congr 1; omega
          rw [e1, ← e2]; ring
      _ = (∑ i ∈ range k, (2 : ℝ) ^ i) * s ^ k := by
          rw [← sum_mul, sum_range_reflect (fun i => (2 : ℝ) ^ i) k]
      _ ≤ 2 ^ k * s ^ k := by
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg hs _)
          rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
          norm_num

theorem edgeFinset'_eq {V : Type} [Fintype V] (G : SimpleGraph V) :
    edgeFinset' G = G.edgeFinset := by
  ext e
  simp [edgeFinset']

end HGA3Aux

open HindsightGain.Uniform.Supplement HGA3Aux in
theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) (ht : 1 ≤ edgeCount G) :
    (∀ J ⊆ edgeFinset' G, J.Nonempty → IsEvenEdgeSet J → 3 ≤ J.card) ∧
    ∀ k : ℕ, 3 ≤ k →
      ((((edgeFinset' G).powerset.filter (fun J => IsEvenEdgeSet J ∧ J.card = k)).card : ℝ) ≤
        (2 * Real.sqrt (2 * (edgeCount G : ℝ))) ^ k) := by
  constructor
  · intro J hJ hne hev
    obtain ⟨v, p, htr, h3, hpJ⟩ := exists_trail G J hJ hne hev
    have hcard : p.edges.toFinset.card = p.length := by
      rw [List.toFinset_card_of_nodup htr.edges_nodup, SimpleGraph.Walk.length_edges]
    have := Finset.card_le_card hpJ
    omega
  · intro k _
    have hE : (edgeCount G : ℝ) = (G.edgeFinset.card : ℝ) := by
      unfold edgeCount; rw [edgeFinset'_eq]
    set s := Real.sqrt (2 * (edgeCount G : ℝ)) with hs
    have key := numeric (fun k => ((evenSets G k).card : ℝ))
      (fun L => ((closedEdgeSets G L).card : ℝ)) s (Real.sqrt_nonneg _)
      (by
        have hsub : evenSets G 0 ⊆ {∅} := by
          intro J hJ
          simp only [evenSets, Finset.mem_filter] at hJ
          rw [Finset.mem_singleton, ← Finset.card_eq_zero]; exact hJ.2.2
        have := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at this
        exact_mod_cast this)
      (fun _ => Nat.cast_nonneg _)
      (fun i => by
        have h1 := card_closedEdgeSets_le G (i + 1)
        have h2 := trace_le G (i + 1) (by omega)
        rw [hs, hE]
        exact h1.trans h2)
      (fun _ => Nat.cast_nonneg _)
      (fun k hk => evenSets_rec G k hk) k
    rw [mul_pow]
    exact key
