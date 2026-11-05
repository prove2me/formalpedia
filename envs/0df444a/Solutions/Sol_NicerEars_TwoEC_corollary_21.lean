-- Prove2me | solution 1 for NicerEars.TwoEC.corollary_21
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:23:12.534874+00:00
-- url     : https://prove2.me/submissions/2a7edb33-2512-4ac1-90b4-c4a6508db0c3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff
import Theorems.Thm_NicerEars_TwoEC_theorem_20

set_option linter.unusedSectionVars false

namespace NicerEars.TwoEC.Aux30

open Finset NicerEars.TwoEC

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

lemma spanGraph_adj (G : Graph V E) (F : Finset E) (u w : V) :
    (G.spanGraph F).Adj u w ↔ u ≠ w ∧ ∃ e ∈ F, G.ends e = s(u, w) := by
  simp only [Graph.spanGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Finset.mem_coe]
  tauto

lemma mem_cut (G : Graph V E) (W : Finset V) (e : E) :
    e ∈ G.cut W ↔ ∃ u ∈ W, ∃ v ∉ W, G.ends e = s(u, v) := by
  simp [Graph.cut]

lemma ends_eq (G : Graph V E) (e : E) : ∃ a b, a ≠ b ∧ G.ends e = s(a, b) := by
  have key : ∀ z : Sym2 V, ¬ z.IsDiag → ∃ a b, a ≠ b ∧ z = s(a, b) := by
    intro z
    induction z using Sym2.ind with
    | _ a b => intro h; exact ⟨a, b, by simpa using h, rfl⟩
  exact key _ (G.loopless e)

lemma mem_cut_singleton (G : Graph V E) (v : V) (e : E) :
    e ∈ G.cut {v} ↔ v ∈ G.ends e := by
  rw [mem_cut]
  obtain ⟨a, b, hab, h⟩ := ends_eq G e
  rw [h]
  constructor
  · rintro ⟨u, hu, w, hw, h'⟩
    rw [mem_singleton] at hu; subst hu
    rw [h']; exact Sym2.mem_mk_left _ _
  · intro hv
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact ⟨v, mem_singleton_self _, b, by simpa [eq_comm] using hab, rfl⟩
    · exact ⟨v, mem_singleton_self _, a, by simpa using hab, Sym2.eq_swap⟩

lemma connected_iff_cut (G : Graph V E) (F : Finset E) [Nonempty V] :
    (G.spanGraph F).Connected ↔
      ∀ W : Finset V, W.Nonempty → W ≠ univ → ∃ e ∈ F, e ∈ G.cut W := by
  constructor
  · intro hc W ⟨u, hu⟩ hW
    obtain ⟨w, hw⟩ : ∃ w, w ∉ W := by
      by_contra h; push Not at h; exact hW (eq_univ_iff_forall.mpr h)
    obtain ⟨p⟩ := hc.preconnected u w
    obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart (W : Set V) hu hw
    have hadj := d.adj
    rw [spanGraph_adj] at hadj
    obtain ⟨-, e, he, hends⟩ := hadj
    exact ⟨e, he, (mem_cut G W e).2 ⟨_, hd1, _, hd2, hends⟩⟩
  · intro h
    rw [SimpleGraph.connected_iff]
    refine ⟨?_, inferInstance⟩
    intro u w
    by_contra hnr
    classical
    let W : Finset V := univ.filter (fun z => (G.spanGraph F).Reachable u z)
    have hWne : W.Nonempty := ⟨u, by simp [W]⟩
    have hWu : W ≠ univ := by
      intro hh
      have : w ∈ W := hh ▸ mem_univ w
      simp [W] at this
      exact hnr this
    obtain ⟨e, he, hcut⟩ := h W hWne hWu
    obtain ⟨a, ha, b, hb, hends⟩ := (mem_cut G W e).1 hcut
    have hab : a ≠ b := fun hab => hb (hab ▸ ha)
    have hadj : (G.spanGraph F).Adj a b := (spanGraph_adj G F a b).2 ⟨hab, e, he, hends⟩
    simp only [W, mem_filter, mem_univ, true_and] at ha hb
    exact hb (ha.trans hadj.reachable)

lemma twoEC_iff_cut (G : Graph V E) (F : Finset E) [Nonempty V] :
    G.IsTwoECSpanning F ↔
      ∀ W : Finset V, W.Nonempty → W ≠ univ →
        ∃ e₁ ∈ F, ∃ e₂ ∈ F, e₁ ≠ e₂ ∧ e₁ ∈ G.cut W ∧ e₂ ∈ G.cut W := by
  unfold Graph.IsTwoECSpanning
  simp only [connected_iff_cut]
  constructor
  · rintro ⟨h1, h2⟩ W hW hWu
    obtain ⟨e, he, hc⟩ := h1 W hW hWu
    obtain ⟨e', he', hc'⟩ := h2 e he W hW hWu
    rw [mem_erase] at he'
    exact ⟨e, he, e', he'.2, he'.1.symm, hc, hc'⟩
  · intro h
    refine ⟨fun W hW hWu => ?_, fun e he W hW hWu => ?_⟩
    · obtain ⟨e, he, -, -, -, hc, -⟩ := h W hW hWu
      exact ⟨e, he, hc⟩
    · obtain ⟨e₁, he₁, e₂, he₂, hne, hc₁, hc₂⟩ := h W hW hWu
      by_cases h1 : e₁ = e
      · exact ⟨e₂, mem_erase.2 ⟨fun h2 => hne (h1.trans h2.symm), he₂⟩, hc₂⟩
      · exact ⟨e₁, mem_erase.2 ⟨h1, he₁⟩, hc₁⟩

lemma cut_of_ends (G : Graph V E) (W : Finset V) (e : E) (u w : V) (h : G.ends e = s(u, w))
    (hu : u ∈ W) (hw : w ∉ W) : e ∈ G.cut W := (mem_cut G W e).2 ⟨u, hu, w, hw, h⟩

lemma cut_of_ends' (G : Graph V E) (W : Finset V) (e : E) (u w : V) (h : G.ends e = s(u, w))
    (hu : u ∉ W) (hw : w ∈ W) : e ∈ G.cut W :=
  (mem_cut G W e).2 ⟨w, hw, u, hu, h.trans Sym2.eq_swap⟩

lemma ne_of_ends (G : Graph V E) (e e' : E) (p q : Sym2 V) (h : G.ends e = p) (h' : G.ends e' = q)
    (hpq : p ≠ q) : e ≠ e' := by
  rintro rfl; exact hpq (h.symm.trans h')



lemma msum (G : Graph V E) (L : Multiset (Finset V)) (x : E → ℝ) :
    (L.map (fun W => ∑ e ∈ G.cut W, x e)).sum =
      ∑ e, x e * (Multiset.card (L.filter (fun W => e ∈ G.cut W)) : ℝ) := by
  induction L using Multiset.induction_on with
  | empty => simp
  | cons a L ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih]
    have : ∑ e ∈ G.cut a, x e = ∑ e, (if e ∈ G.cut a then x e else 0) := by
      rw [Finset.sum_ite_mem, univ_inter]
    rw [this, ← sum_add_distrib]
    refine sum_congr rfl (fun e _ => ?_)
    by_cases h : e ∈ G.cut a
    · rw [Multiset.filter_cons_of_pos (p := fun W => e ∈ G.cut W) L h, Multiset.card_cons,
        if_pos h]; push_cast; ring
    · rw [Multiset.filter_cons_of_neg (p := fun W => e ∈ G.cut W) L h, if_neg h]; ring

lemma feasible_of_twoEC (G : Graph V E) (F : Finset E) (hF : G.IsTwoECSpanning F) :
    G.LPFeasible (fun e => if e ∈ F then (1 : ℝ) else 0) := by
  have : Nonempty V := hF.1.nonempty
  rw [twoEC_iff_cut] at hF
  refine ⟨fun e => by dsimp only; split_ifs <;> norm_num, fun W hW hWu => ?_⟩
  obtain ⟨a, ha, b, hb, hab, hac, hbc⟩ := hF W hW hWu
  rw [Finset.sum_ite_mem]
  simp only [sum_const, nsmul_eq_mul, mul_one]
  have : 1 < #(G.cut W ∩ F) := one_lt_card.2 ⟨a, mem_inter.2 ⟨hac, ha⟩, b,
    mem_inter.2 ⟨hbc, hb⟩, hab⟩
  exact_mod_cast this


lemma cut_iff_of_ends (G : Graph V E) (W : Finset V) (e : E) (p q : V) (h : G.ends e = s(p, q)) :
    e ∈ G.cut W ↔ (p ∈ W ∧ q ∉ W) ∨ (q ∈ W ∧ p ∉ W) := by
  rw [mem_cut]
  constructor
  · rintro ⟨u, hu, w, hw, h'⟩
    rw [h, Sym2.eq_iff] at h'
    rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hu, hw⟩
    · exact Or.inr ⟨hu, hw⟩
  · rintro (⟨hp, hq⟩ | ⟨hq, hp⟩)
    · exact ⟨p, hp, q, hq, h⟩
    · exact ⟨q, hq, p, hp, h.trans Sym2.eq_swap⟩

/-- For a feasible point of `LP(G)`, the partition constraints of `LP(G, T)` hold:
`x(δ(𝒲)) ≥ |𝒲| - 1`. -/
lemma partition_bound (G : Graph V E) (x : E → ℝ) (hx : G.LPFeasible x)
    (P : Finpartition (univ : Finset V)) :
    (#P.parts : ℝ) - 1 ≤ ∑ e ∈ G.crossing P, x e := by
  have hnn : 0 ≤ ∑ e ∈ G.crossing P, x e := sum_nonneg (fun e _ => hx.1 e)
  by_cases hk : #P.parts ≤ 1
  · have : (#P.parts : ℝ) ≤ 1 := by exact_mod_cast hk
    linarith
  push Not at hk
  -- every part is a nonempty proper subset
  have hproper : ∀ p ∈ P.parts, p.Nonempty ∧ p ≠ univ := by
    intro p hp
    refine ⟨P.nonempty_of_mem_parts hp, ?_⟩
    obtain ⟨q, hq, hqp⟩ := exists_mem_ne hk p
    intro hpu
    obtain ⟨z, hz⟩ := P.nonempty_of_mem_parts hq
    have hd := P.disjoint hq hp hqp
    exact disjoint_left.1 hd hz (hpu ▸ mem_univ z)
  have hlow : (#P.parts : ℝ) * 2 ≤ ∑ p ∈ P.parts, ∑ e ∈ G.cut p, x e := by
    calc (#P.parts : ℝ) * 2 = ∑ _p ∈ P.parts, (2 : ℝ) := by simp
      _ ≤ _ := sum_le_sum (fun p hp => hx.2 p (hproper p hp).1 (hproper p hp).2)
  have hcount : ∀ e : E, #(P.parts.filter (fun p => e ∈ G.cut p)) ≤
      (if e ∈ G.crossing P then 2 else 0) := by
    intro e
    obtain ⟨u, v, huv, he⟩ := ends_eq G e
    have hsub : P.parts.filter (fun p => e ∈ G.cut p) ⊆ {P.part u, P.part v} := by
      intro p hp
      rw [mem_filter] at hp
      rw [cut_iff_of_ends G p e u v he] at hp
      rcases hp.2 with ⟨hu, -⟩ | ⟨hv, -⟩
      · simp [P.part_eq_of_mem hp.1 hu]
      · simp [P.part_eq_of_mem hp.1 hv]
    split_ifs with hc
    · exact (card_le_card hsub).trans card_le_two
    · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
      intro p hp hcut
      apply hc
      unfold NicerEars.TwoEC.Graph.crossing
      rw [mem_filter]
      refine ⟨mem_univ _, u, v, he, ?_⟩
      rw [cut_iff_of_ends G p e u v he] at hcut
      rcases hcut with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rw [P.part_eq_of_mem hp hu]
        intro h; exact hv (h ▸ (P.mem_part_self.2 (mem_univ v)))
      · rw [P.part_eq_of_mem hp hv]
        intro h; exact hu (h ▸ (P.mem_part_self.2 (mem_univ u)))
  have hup : ∑ p ∈ P.parts, ∑ e ∈ G.cut p, x e ≤ 2 * ∑ e ∈ G.crossing P, x e := by
    have : ∀ p ∈ P.parts, ∑ e ∈ G.cut p, x e = ∑ e, (if e ∈ G.cut p then x e else 0) := by
      intro p _; rw [Finset.sum_ite_mem, univ_inter]
    rw [sum_congr rfl this, sum_comm]
    have h2 : 2 * ∑ e ∈ G.crossing P, x e = ∑ e, (if e ∈ G.crossing P then 2 * x e else 0) := by
      rw [Finset.sum_ite_mem, univ_inter, mul_sum]
    rw [h2]
    refine sum_le_sum (fun e _ => ?_)
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    have hc := hcount e
    split_ifs at hc ⊢ with h
    · have : (#(P.parts.filter (fun p => e ∈ G.cut p)) : ℝ) ≤ 2 := by exact_mod_cast hc
      nlinarith [hx.1 e]
    · have : #(P.parts.filter (fun p => e ∈ G.cut p)) = 0 := by omega
      rw [this]; simp
  linarith

lemma lpT_of_lp (G : Graph V E) (x : E → ℝ) (hx : G.LPFeasible x) : G.LPTFeasible ∅ x :=
  ⟨hx.1, fun W hW hWu _ => hx.2 W hW hWu, fun P => partition_bound G x hx P⟩

end NicerEars.TwoEC.Aux30

open Finset NicerEars.TwoEC NicerEars.TwoEC.Aux30 in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TwoEC.Graph V E) (hG : G.IsTwoEdgeConnected) (M : Finset (Finset V))
    (hM : IsEardrum G M) (hP : ∀ f ∈ M, (PathsThrough G f).Nonempty) :
    (∀ x : E → ℝ, G.LPFeasible x → (Lmu G M : ℝ) ≤ ∑ e, x e) ∧
      ∀ F : Finset E, G.IsTwoECSpanning F → Lmu G M ≤ #F := by
  have h20 := (theorem_20 G hG.1 ∅ (by simp) M hM (fun f _ => disjoint_empty_right f) hP).1
  have part1 : ∀ x : E → ℝ, G.LPFeasible x → (Lmu G M : ℝ) ≤ ∑ e, x e :=
    fun x hx => h20 x (lpT_of_lp G x hx)
  refine ⟨part1, fun F hF => ?_⟩
  have := part1 _ (feasible_of_twoEC G F hF)
  rw [Finset.sum_ite_mem, univ_inter] at this
  simp only [sum_const, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this
