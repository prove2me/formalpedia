-- Prove2me | solution 1 for NicerEars.TwoEC.theorem_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:18:48.108274+00:00
-- url     : https://prove2.me/submissions/36f78bb9-07e2-44c4-adab-3f2149d501f2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff
import Theorems.Thm_NicerEars_TwoEC_theorem_7
import Theorems.Thm_NicerEars_TwoEC_tcut_two_packing

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

end NicerEars.TwoEC.Aux30

open Finset NicerEars.TwoEC NicerEars.TwoEC.Aux30 in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TwoEC.Graph V E) (hG : G.IsTwoEdgeConnected) :
    (∀ x : E → ℝ, G.LPFeasible x → (Lphi G : ℝ) ≤ ∑ e, x e) ∧
      ∀ F : Finset E, G.IsTwoECSpanning F → Lphi G ≤ #F := by
  obtain ⟨T, hT, hτ⟩ := (theorem_7 G hG).1
  obtain ⟨L, hLc, hodd, hcov⟩ := tcut_two_packing G hG.1 T hT
  have hL : (Lphi G : ℝ) = Multiset.card L := by
    unfold Lphi; rw [hLc]; push_cast
    have : ((2 * G.tau T : ℤ) : ℝ) = ((Fintype.card V + G.phi - 1 : ℤ) : ℝ) := by
      exact_mod_cast hτ
    push_cast at this; linarith
  have part1 : ∀ x : E → ℝ, G.LPFeasible x → (Lphi G : ℝ) ≤ ∑ e, x e := by
    intro x hx
    have hlow : 2 * (Multiset.card L : ℝ) ≤ (L.map (fun W => ∑ e ∈ G.cut W, x e)).sum := by
      have : ∀ W ∈ L, (2 : ℝ) ≤ ∑ e ∈ G.cut W, x e := by
        intro W hW
        have ho := hodd W hW
        refine hx.2 W ?_ ?_
        · by_contra hne
          rw [not_nonempty_iff_eq_empty] at hne
          rw [hne, empty_inter, card_empty] at ho
          exact (Nat.not_odd_zero) ho
        · intro hu
          rw [hu, univ_inter] at ho
          exact (Nat.not_odd_iff_even.2 hT) ho
      have := Multiset.card_nsmul_le_sum (s := L.map (fun W => ∑ e ∈ G.cut W, x e)) (a := 2)
        (by intro y hy; obtain ⟨W, hW, rfl⟩ := Multiset.mem_map.1 hy; exact this W hW)
      simpa [mul_comm] using this
    have hup : (L.map (fun W => ∑ e ∈ G.cut W, x e)).sum ≤ 2 * ∑ e, x e := by
      rw [msum, mul_sum]
      refine sum_le_sum (fun e _ => ?_)
      have := hcov e
      have h2 : (Multiset.card (L.filter (fun W => e ∈ G.cut W)) : ℝ) ≤ 2 := by exact_mod_cast this
      rw [mul_comm 2]
      exact mul_le_mul_of_nonneg_left h2 (hx.1 e)
    rw [hL]; linarith
  refine ⟨part1, fun F hF => ?_⟩
  have := part1 _ (feasible_of_twoEC G F hF)
  rw [Finset.sum_ite_mem, univ_inter] at this
  simp only [sum_const, nsmul_eq_mul, mul_one] at this
  exact_mod_cast this
