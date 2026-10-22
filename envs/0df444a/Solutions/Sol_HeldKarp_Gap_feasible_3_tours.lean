-- Prove2me | solution 1 for HeldKarp.Gap.feasible_3_tours
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:37:37.631971+00:00
-- url     : https://prove2.me/submissions/53658797-f5d7-4db7-9d30-a569ff6242b4

import Mathlib
import Definitions.Def_HeldKarp_Ascent_IsOneTree
import Definitions.Def_HeldKarp_Gap_SubtourLP

open Classical
open HeldKarp.Ascent
open HeldKarp.Gap

theorem g71x_deg_incidence {n : ℕ} (G : SimpleGraph (Fin n)) (i : Fin n) :
    deg (incidence G) i = G.degree i := by
  unfold deg incidence
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.filter_filter, ← SimpleGraph.card_incidenceFinset_eq_degree]
  congr 1
  refine Finset.card_bij (fun e _ => e.1) ?_ ?_ ?_
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
    rw [SimpleGraph.mem_incidenceFinset]
    exact ⟨he.2, he.1⟩
  · intro e₁ _ e₂ _ h; exact Subtype.ext h
  · intro e he
    rw [SimpleGraph.mem_incidenceFinset] at he
    refine ⟨⟨e, G.not_isDiag_of_mem_edgeSet he.1⟩, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨he.2, he.1⟩

theorem g71x_sum_deg {n : ℕ} (x : Edge n → ℝ) (S : Finset (Fin n)) :
    ∑ v ∈ S, deg x v = ∑ e : Edge n, x e * ((S.filter (fun v => v ∈ e.1)).card : ℝ) := by
  unfold deg
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

theorem g71x_card_le_two {n : ℕ} (S : Finset (Fin n)) (e : Sym2 (Fin n)) :
    (S.filter (fun v => v ∈ e)).card ≤ 2 := by
  induction e using Sym2.ind with
  | h a b =>
    calc (S.filter (fun v => v ∈ s(a, b))).card ≤ ({a, b} : Finset (Fin n)).card := by
          apply Finset.card_le_card
          intro v hv
          simp only [Finset.mem_filter, Sym2.mem_iff] at hv
          rcases hv.2 with h | h <;> simp [h]
      _ ≤ 2 := Finset.card_le_two

theorem g71x_card_inside {n : ℕ} (S : Finset (Fin n)) (e : Sym2 (Fin n)) (he : ¬ e.IsDiag)
    (hin : ∀ v ∈ e, v ∈ S) : (S.filter (fun v => v ∈ e)).card = 2 := by
  induction e using Sym2.ind with
  | h a b =>
    have hab : a ≠ b := by simpa using he
    have : S.filter (fun v => v ∈ s(a, b)) = {a, b} := by
      ext v
      simp only [Finset.mem_filter, Sym2.mem_iff, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with rfl | rfl
        · exact hin _ (Sym2.mem_mk_left _ _)
        · exact hin _ (Sym2.mem_mk_right _ _)
    rw [this, Finset.card_pair hab]

theorem g71x_card_meet {n : ℕ} (S : Finset (Fin n)) (e : Sym2 (Fin n)) (v : Fin n) (hv : v ∈ e)
    (hvS : v ∈ S) : 1 ≤ (S.filter (fun v => v ∈ e)).card :=
  Finset.card_pos.2 ⟨v, Finset.mem_filter.2 ⟨hvS, hv⟩⟩

/-- lower bound: Σ_{v∈S} deg ≥ 2 insideSum + x e₀ for a crossing edge e₀ -/
theorem g71x_sum_deg_ge {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e) (S : Finset (Fin n))
    (e₀ : Edge n) (h₀ : ∃ v ∈ e₀.1, v ∈ S) (h₀' : ∃ v ∈ e₀.1, v ∉ S) :
    2 * insideSum x S + x e₀ ≤ ∑ v ∈ S, deg x v := by
  rw [g71x_sum_deg]
  unfold insideSum
  rw [Finset.mul_sum, Finset.sum_filter]
  have hnot : ¬ ∀ v ∈ e₀.1, v ∈ S := by
    obtain ⟨v, hv, hvS⟩ := h₀'; exact fun h => hvS (h v hv)
  have hpt : ∀ e : Edge n, (if ∀ v ∈ e.1, v ∈ S then 2 * x e else 0) +
      (if e = e₀ then x e else 0) ≤ x e * ((S.filter (fun v => v ∈ e.1)).card : ℝ) := by
    intro e
    by_cases he : e = e₀
    · subst he
      rw [if_neg hnot, if_pos rfl, zero_add]
      obtain ⟨v, hv, hvS⟩ := h₀
      have := g71x_card_meet S e.1 v hv hvS
      have : (1 : ℝ) ≤ ((S.filter (fun v => v ∈ e.1)).card : ℝ) := by exact_mod_cast this
      nlinarith [hx e]
    · rw [if_neg he, add_zero]
      split_ifs with hin
      · rw [g71x_card_inside S e.1 e.2 hin]; push_cast; linarith
      · exact mul_nonneg (hx e) (Nat.cast_nonneg _)
  have := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hpt e)
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq'] at this
  simpa using this

/-- upper bound when no edge of positive weight crosses S -/
theorem g71x_sum_deg_le {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e) (S : Finset (Fin n))
    (hcl : ∀ e : Edge n, x e ≠ 0 → (∃ v ∈ e.1, v ∈ S) → ∀ v ∈ e.1, v ∈ S) :
    ∑ v ∈ S, deg x v ≤ 2 * insideSum x S := by
  rw [g71x_sum_deg]
  unfold insideSum
  rw [Finset.mul_sum, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro e _
  by_cases hx0 : x e = 0
  · rw [hx0]; split_ifs <;> simp
  split_ifs with hin
  · rw [g71x_card_inside S e.1 e.2 hin]; push_cast; linarith
  · have : S.filter (fun v => v ∈ e.1) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hvS hv
      exact hin (hcl e hx0 ⟨v, hv, hvS⟩)
    rw [this]; simp

theorem g71x_incidence_nonneg {n : ℕ} (G : SimpleGraph (Fin n)) (e : Edge n) :
    0 ≤ incidence G e := by unfold incidence; split_ifs <;> norm_num

theorem g71x_insideSum_int {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) :
    ∃ k : ℕ, insideSum (incidence G) S = k := by
  unfold insideSum incidence
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ⟨_, rfl⟩

theorem g71x_incidence_val {n : ℕ} (G : SimpleGraph (Fin n)) (e : Edge n) :
    incidence G e = 0 ∨ incidence G e = 1 := by unfold incidence; split_ifs <;> simp

theorem g71x_closed_mem {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (hS : ∀ a b, a ∈ S → G.Adj a b → b ∈ S) (e : Sym2 (Fin n)) (he : e ∈ G.edgeSet)
    (a : Fin n) (ha : a ∈ e) (haS : a ∈ S) : ∀ u ∈ e, u ∈ S := by
  induction e using Sym2.ind with
  | h p q =>
    rw [SimpleGraph.mem_edgeSet] at he
    intro u hu
    rw [Sym2.mem_iff] at ha hu
    rcases ha with rfl | rfl <;> rcases hu with rfl | rfl
    · exact haS
    · exact hS _ _ haS he
    · exact hS _ _ haS he.symm
    · exact haS

theorem solution {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    Set.BijOn (incidence (n := n)) {H : SimpleGraph (Fin n) | IsTour H}
      {x : Edge n → ℝ | Feasible3 x} := by
  refine ⟨?_, ?_, ?_⟩
  · -- MapsTo
    intro G hG
    obtain ⟨hconn, hdeg⟩ := hG
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; rw [g71x_deg_incidence, hdeg]; norm_num
    · intro S hSne hSsub
      obtain ⟨v, hv⟩ := hSne
      have h0S : (0 : Fin n) ∉ S := fun h => by
        have := hSsub.1 h; simp at this
      obtain ⟨d, -, hd1, hd2⟩ := (hconn.preconnected v 0).some.exists_boundary_dart
        (↑S : Set (Fin n)) hv h0S
      set e₀ : Edge n := ⟨s(d.fst, d.snd), by simpa using d.adj.ne⟩ with he₀
      have hx1 : incidence G e₀ = 1 := by
        unfold incidence; rw [if_pos]; exact d.adj
      have := g71x_sum_deg_ge (incidence G) (g71x_incidence_nonneg G) S e₀
        ⟨d.fst, Sym2.mem_mk_left _ _, hd1⟩ ⟨d.snd, Sym2.mem_mk_right _ _, hd2⟩
      simp_rw [g71x_deg_incidence, hdeg] at this
      rw [hx1, Finset.sum_const, nsmul_eq_mul] at this
      obtain ⟨k, hk⟩ := g71x_insideSum_int G S
      rw [hk] at this ⊢
      have : 2 * k + 1 ≤ S.card * 2 := by exact_mod_cast this
      have : k + 1 ≤ S.card := by omega
      have : ((k + 1 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    · intro e; rcases g71x_incidence_val G e with h | h <;> rw [h] <;> norm_num
    · intro e; rcases g71x_incidence_val G e with h | h <;> rw [h]
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  · -- InjOn
    intro G _ G' _ hGG
    ext u v
    by_cases huv : u = v
    · subst huv; simp
    · have := congrFun hGG ⟨s(u, v), by simpa using huv⟩
      unfold incidence at this
      simp only [SimpleGraph.mem_edgeSet] at this
      constructor
      · intro h; rw [if_pos h] at this; by_contra h'; rw [if_neg h'] at this; norm_num at this
      · intro h; rw [if_pos h] at this; by_contra h'; rw [if_neg h'] at this; norm_num at this
  · -- SurjOn
    intro x hx
    obtain ⟨hdx, hsub, hbd, hint⟩ := hx
    have h01 : ∀ e, x e = 0 ∨ x e = 1 := by
      intro e
      obtain ⟨z, hz⟩ := hint e
      have h1 := (hbd e).1; have h2 := (hbd e).2
      rw [hz] at h1 h2
      have : (0 : ℤ) ≤ z := by exact_mod_cast h1
      have : z ≤ (1 : ℤ) := by exact_mod_cast h2
      rcases (show z = 0 ∨ z = 1 by omega) with h | h
      · left; rw [hz, h]; simp
      · right; rw [hz, h]; simp
    set G : SimpleGraph (Fin n) :=
      SimpleGraph.fromEdgeSet {e | ∃ h : ¬ e.IsDiag, x ⟨e, h⟩ = 1} with hG
    have hmem : ∀ e : Edge n, e.1 ∈ G.edgeSet ↔ x e = 1 := by
      intro e
      rw [hG, SimpleGraph.edgeSet_fromEdgeSet]
      constructor
      · rintro ⟨⟨_, h⟩, -⟩; exact h
      · intro h1; exact ⟨⟨e.2, h1⟩, e.2⟩
    have hinc : incidence G = x := by
      funext e
      unfold incidence
      split_ifs with h
      · exact ((hmem e).1 h).symm
      · rcases h01 e with h' | h'
        · exact h'.symm
        · exact absurd ((hmem e).2 h') h
    refine ⟨G, ⟨?_, ?_⟩, hinc⟩
    · -- connected
      have hdegG : ∀ i, G.degree i = 2 := by
        intro i
        have := g71x_deg_incidence G i
        rw [hinc, hdx] at this
        have h2 := this.symm
        norm_cast at h2
        convert h2
      have : Nonempty (Fin n) := ⟨0⟩
      rw [SimpleGraph.connected_iff]
      refine ⟨?_, inferInstance⟩
      by_contra hpc
      have : ∃ v, ¬ G.Reachable 0 v := by
        by_contra hall
        push Not at hall
        exact hpc (fun u w => ((hall u).symm).trans (hall w))
      obtain ⟨v, hv⟩ := this
      set S : Finset (Fin n) := Finset.univ.filter (fun w => G.Reachable v w) with hSdef
      have hvS : v ∈ S := by simp [hSdef]
      have h0S : (0 : Fin n) ∉ S := by
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun h => hv h.symm
      have hcl : ∀ a b, a ∈ S → G.Adj a b → b ∈ S := by
        intro a b ha hab
        simp only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
        exact ha.trans hab.reachable
      have hsubS : S ⊆ Finset.univ.erase 0 := by
        intro w hw
        rw [Finset.mem_erase]
        exact ⟨fun h => h0S (h ▸ hw), Finset.mem_univ _⟩
      have hne : S ≠ Finset.univ.erase 0 := by
        intro hSe
        have hpos : 0 < G.degree 0 := by rw [hdegG]; norm_num
        obtain ⟨w, hw⟩ := (G.degree_pos_iff_exists_adj 0).1 (by convert hpos)
        have hwS : w ∈ S := by rw [hSe, Finset.mem_erase]; exact ⟨hw.ne.symm, Finset.mem_univ _⟩
        exact h0S (hcl w 0 hwS hw.symm)
      have hb := hsub S ⟨v, hvS⟩ (Finset.ssubset_iff_subset_ne.2 ⟨hsubS, hne⟩)
      have hle := g71x_sum_deg_le x (fun e => (hbd e).1) S (by
        intro e hxe hmeet
        have he : e.1 ∈ G.edgeSet := by
          have : incidence G e ≠ 0 := by rw [hinc]; exact hxe
          unfold incidence at this
          by_contra h; rw [if_neg h] at this; exact this rfl
        obtain ⟨a, ha, haS⟩ := hmeet
        exact g71x_closed_mem G S hcl e.1 he a ha haS)
      simp_rw [hdx] at hle
      rw [Finset.sum_const, nsmul_eq_mul] at hle
      linarith
    · intro i
      have := g71x_deg_incidence G i
      rw [hinc, hdx] at this
      have h2 := this.symm
      norm_cast at h2
