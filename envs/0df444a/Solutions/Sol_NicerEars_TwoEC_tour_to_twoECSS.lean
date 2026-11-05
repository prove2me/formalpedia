-- Prove2me | solution 1 for NicerEars.TwoEC.tour_to_twoECSS
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:03:05.549652+00:00
-- url     : https://prove2.me/submissions/364e9817-1025-4962-b0c5-61fa2228ccce

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting

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


lemma exists_not_mem {α : Type} [Fintype α] (s : Finset α) (h : #s < Fintype.card α) :
    ∃ c, c ∉ s := by
  by_contra hc; push Not at hc
  have : s = univ := eq_univ_iff_forall.mpr hc
  rw [this, card_univ] at h; omega

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

/-- Handshake parity: if all degrees in `F` are even, every cut meets `F` evenly. -/
lemma even_cut (G : Graph V E) (F : Finset E) (hF : ∀ v, Even #(F.filter (fun e => v ∈ G.ends e)))
    (W : Finset V) : Even #(F.filter (fun e => e ∈ G.cut W)) := by
  classical
  have key : ∀ f : E, #(W.filter (fun v => v ∈ G.ends f)) =
      (if f ∈ G.cut W then 1 else 0) + 2 * (if (∀ z, z ∈ G.ends f → z ∈ W) then 1 else 0) := by
    intro f
    obtain ⟨p, q, hpq, h⟩ := ends_eq G f
    have hc := cut_iff_of_ends G W f p q h
    have hin : (∀ z, z ∈ G.ends f → z ∈ W) ↔ p ∈ W ∧ q ∈ W := by
      rw [h]; constructor
      · intro hz; exact ⟨hz p (Sym2.mem_mk_left _ _), hz q (Sym2.mem_mk_right _ _)⟩
      · rintro ⟨hp, hq⟩ z hz; rcases Sym2.mem_iff.1 hz with rfl | rfl <;> assumption
    have hfil : W.filter (fun v => v ∈ G.ends f) = W ∩ {p, q} := by
      ext z; simp [h, Sym2.mem_iff, and_comm]
    rw [hfil]
    by_cases hp : p ∈ W <;> by_cases hq : q ∈ W
    · have : W ∩ {p, q} = {p, q} := by
        ext z; simp only [mem_inter, mem_insert, mem_singleton]
        constructor
        · exact fun h => h.2
        · rintro (rfl | rfl) <;> simp_all
      rw [this, card_pair hpq, if_neg (by tauto), if_pos (by tauto)]
    · have : W ∩ {p, q} = {p} := by
        ext z; simp only [mem_inter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hz, rfl | rfl⟩; rfl; exact absurd hz hq
        · rintro rfl; exact ⟨hp, Or.inl rfl⟩
      rw [this, card_singleton, if_pos (by tauto), if_neg (by tauto)]
    · have : W ∩ {p, q} = {q} := by
        ext z; simp only [mem_inter, mem_insert, mem_singleton]
        constructor
        · rintro ⟨hz, rfl | rfl⟩; exact absurd hz hp; rfl
        · rintro rfl; exact ⟨hq, Or.inr rfl⟩
      rw [this, card_singleton, if_pos (by tauto), if_neg (by tauto)]
    · have : W ∩ {p, q} = ∅ := by
        ext z; simp only [mem_inter, mem_insert, mem_singleton, Finset.notMem_empty, iff_false]
        rintro ⟨hz, rfl | rfl⟩ <;> contradiction
      rw [this, card_empty, if_neg (by tauto), if_neg (by tauto)]
  have hsum : ∑ v ∈ W, #(F.filter (fun e => v ∈ G.ends e)) =
      #(F.filter (fun e => e ∈ G.cut W)) +
        2 * #(F.filter (fun e => ∀ z, z ∈ G.ends e → z ∈ W)) := by
    simp_rw [card_filter]
    rw [Finset.sum_comm]
    simp_rw [← card_filter, key, sum_add_distrib, ← mul_sum, ← card_filter]
  have hev : Even (∑ v ∈ W, #(F.filter (fun e => v ∈ G.ends e))) :=
    Finset.even_sum _ (fun v _ => hF v)
  rw [hsum] at hev
  exact (Nat.even_add.1 hev).2 (even_two_mul _)


lemma cut_congr_of (G : Graph V E) (W W' : Finset V)
    (h : (∀ z, (z ∈ W ↔ z ∈ W')) ∨ (∀ z, (z ∈ W ↔ z ∉ W'))) (f : E) :
    f ∈ G.cut W ↔ f ∈ G.cut W' := by
  obtain ⟨p, q, -, hf⟩ := ends_eq G f
  rw [cut_iff_of_ends G W f p q hf, cut_iff_of_ends G W' f p q hf]
  rcases h with h | h
  · rw [h p, h q]
  · rw [h p, h q]; tauto

/-- If two cuts meet a connected edge set `S` in the same edges, the cuts are equal or
complementary. -/
lemma cut_unique (G : Graph V E) (S : Finset E) [Nonempty V] (hS : (G.spanGraph S).Connected)
    (W W' : Finset V) (h : ∀ s ∈ S, (s ∈ G.cut W ↔ s ∈ G.cut W')) :
    (∀ z, (z ∈ W ↔ z ∈ W')) ∨ (∀ z, (z ∈ W ↔ z ∉ W')) := by
  classical
  let Z : Finset V := univ.filter (fun z => ¬ ((z ∈ W) ↔ (z ∈ W')))
  have hZ : ∀ s ∈ S, s ∉ G.cut Z := by
    intro s hs hsZ
    obtain ⟨p, q, -, hf⟩ := ends_eq G s
    have h1 := h s hs
    rw [cut_iff_of_ends G W s p q hf, cut_iff_of_ends G W' s p q hf] at h1
    rw [cut_iff_of_ends G Z s p q hf] at hsZ
    simp only [Z, mem_filter, mem_univ, true_and] at hsZ
    tauto
  rw [connected_iff_cut] at hS
  by_cases hne : Z.Nonempty
  · by_cases hu : Z = univ
    · right; intro z
      have : z ∈ Z := hu ▸ mem_univ z
      simp only [Z, mem_filter, mem_univ, true_and] at this
      tauto
    · obtain ⟨s, hs, hsc⟩ := hS Z hne hu
      exact absurd hsc (hZ s hs)
  · left; intro z
    by_contra hz
    exact hne ⟨z, by simp only [Z, mem_filter, mem_univ, true_and]; exact hz⟩

end NicerEars.TwoEC.Aux30

open Finset NicerEars.TwoEC.Aux30 in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TwoEC.Graph V E) (hG : G.IsTwoEdgeConnected) (F : Finset (E × Fin 2))
    (hF : G.IsTour F) :
    ∃ F' : Finset E, G.IsTwoECSpanning F' ∧ #F' ≤ #F := by
  classical
  obtain ⟨hTJ, hconn⟩ := hF
  have heven : ∀ v, Even #(F.filter (fun p => v ∈ G.double.ends p)) := by
    intro v
    rw [← Nat.not_odd_iff_even]
    intro h
    have := (hTJ v).1 h
    simp at this
  set S : Finset E := F.image Prod.fst with hSdef
  have hSconn : (G.spanGraph S).Connected := by
    have : G.spanGraph S = G.double.spanGraph F := by
      ext u w
      rw [spanGraph_adj, spanGraph_adj]
      simp only [hSdef, mem_image, NicerEars.TwoEC.Graph.double]
      constructor
      · rintro ⟨huw, e, ⟨p, hp, rfl⟩, he⟩; exact ⟨huw, p, hp, he⟩
      · rintro ⟨huw, p, hp, he⟩; exact ⟨huw, p.1, ⟨p, hp, rfl⟩, he⟩
    rw [this]; exact hconn
  have hne : Nonempty V := hSconn.nonempty
  -- multiplicities
  let mult : E → ℕ := fun e => #(F.filter (fun p => p.1 = e))
  have hmult_le : ∀ e, mult e ≤ 2 := by
    intro e
    have : F.filter (fun p => p.1 = e) ⊆ {(e, 0), (e, 1)} := by
      intro p hp
      rw [mem_filter] at hp
      rcases p with ⟨a, i⟩
      simp only at hp
      obtain ⟨-, rfl⟩ := hp
      fin_cases i <;> simp
    exact (card_le_card this).trans card_le_two
  have hmult_pos : ∀ e ∈ S, 1 ≤ mult e := by
    intro e he
    rw [hSdef, mem_image] at he
    obtain ⟨p, hp, rfl⟩ := he
    exact card_pos.2 ⟨p, mem_filter.2 ⟨hp, rfl⟩⟩
  have hcardF : #F = ∑ e ∈ S, mult e := card_eq_sum_card_image Prod.fst F
  let D : Finset E := S.filter (fun e => mult e = 2)
  have hcardF' : #F = #S + #D := by
    rw [hcardF, card_filter, card_eq_sum_ones S, ← sum_add_distrib]
    refine sum_congr rfl (fun e he => ?_)
    have h1 := hmult_pos e he; have h2 := hmult_le e
    split_ifs with h <;> omega
  -- bridges of S are doubled
  let Br : E → Prop := fun e =>
    ∃ W : Finset V, W.Nonempty ∧ W ≠ univ ∧ S.filter (fun s => s ∈ G.cut W) = {e}
  have hBrD : ∀ e ∈ S, Br e → mult e = 2 := by
    rintro e heS ⟨W, -, -, hW⟩
    have hev := even_cut G.double F heven W
    have : F.filter (fun p => p ∈ G.double.cut W) = F.filter (fun p => p.1 = e) := by
      ext p
      simp only [mem_filter]
      have hc : p ∈ G.double.cut W ↔ p.1 ∈ G.cut W := by
        rw [mem_cut, mem_cut]; rfl
      rw [hc]
      constructor
      · rintro ⟨hp, hpc⟩
        refine ⟨hp, ?_⟩
        have : p.1 ∈ S.filter (fun s => s ∈ G.cut W) :=
          mem_filter.2 ⟨mem_image_of_mem _ hp, hpc⟩
        rw [hW] at this; simpa using this
      · rintro ⟨hp, rfl⟩
        refine ⟨hp, ?_⟩
        have : p.1 ∈ S.filter (fun s => s ∈ G.cut W) := by rw [hW]; simp
        exact (mem_filter.1 this).2
    rw [this] at hev
    have h1 := hmult_pos e heS; have h2 := hmult_le e
    change Even (mult e) at hev
    rcases hev with ⟨k, hk⟩; omega
  have hgex : ∀ e, Br e → ∃ W : Finset V, (W.Nonempty ∧ W ≠ univ ∧
      S.filter (fun s => s ∈ G.cut W) = {e}) ∧ ∃ g, g ∈ G.cut W ∧ g ≠ e := by
    rintro e ⟨W, hW1, hW2, hW3⟩
    refine ⟨W, ⟨hW1, hW2, hW3⟩, ?_⟩
    have h2 := hG
    unfold NicerEars.TwoEC.Graph.IsTwoEdgeConnected at h2
    rw [twoEC_iff_cut] at h2
    obtain ⟨e₁, -, e₂, -, hne', h₁, h₂⟩ := h2 W hW1 hW2
    by_cases h : e₁ = e
    · exact ⟨e₂, h₂, fun h' => hne' (h.trans h'.symm)⟩
    · exact ⟨e₁, h₁, h⟩
  choose Wf hWf gf hgf using hgex
  let g : E → E := fun e => if h : Br e then gf e h else e
  let Bset : Finset E := S.filter Br
  refine ⟨S ∪ Bset.image g, ?_, ?_⟩
  · rw [twoEC_iff_cut]
    intro W hW hWu
    obtain ⟨e, heS, hec⟩ := (connected_iff_cut G S).1 hSconn W hW hWu
    by_cases h2 : ∃ e' ∈ S, e' ∈ G.cut W ∧ e' ≠ e
    · obtain ⟨e', he'S, he'c, hne'⟩ := h2
      exact ⟨e, mem_union_left _ heS, e', mem_union_left _ he'S, hne'.symm, hec, he'c⟩
    · push Not at h2
      have hfil : S.filter (fun s => s ∈ G.cut W) = {e} := by
        ext s; simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hs, hsc⟩; exact h2 s hs hsc
        · rintro rfl; exact ⟨heS, hec⟩
      have hBr : Br e := ⟨W, hW, hWu, hfil⟩
      obtain ⟨-, -, hW'⟩ := hWf e hBr
      obtain ⟨hgc, hgne⟩ := hgf e hBr
      have huniq := cut_unique G S hSconn W (Wf e hBr) (by
        intro s hs
        have a1 : s ∈ G.cut W ↔ s = e := by
          have := congrArg (s ∈ ·) hfil; simp only [mem_filter, mem_singleton, eq_iff_iff] at this
          constructor
          · intro hc; exact this.1 ⟨hs, hc⟩
          · intro hse; exact (this.2 hse).2
        have a2 : s ∈ G.cut (Wf e hBr) ↔ s = e := by
          have := congrArg (s ∈ ·) hW'; simp only [mem_filter, mem_singleton, eq_iff_iff] at this
          constructor
          · intro hc; exact this.1 ⟨hs, hc⟩
          · intro hse; exact (this.2 hse).2
        rw [a1, a2])
      have hgW : gf e hBr ∈ G.cut W := (cut_congr_of G W (Wf e hBr) huniq _).2 hgc
      refine ⟨e, mem_union_left _ heS, gf e hBr, mem_union_right _ ?_, hgne.symm, hec, hgW⟩
      rw [mem_image]
      exact ⟨e, mem_filter.2 ⟨heS, hBr⟩, by simp [g, hBr]⟩
  · have hB : #Bset ≤ #D := by
      apply card_le_card
      intro e he
      rw [mem_filter] at he ⊢
      exact ⟨he.1, hBrD e he.1 he.2⟩
    calc #(S ∪ Bset.image g) ≤ #S + #(Bset.image g) := card_union_le _ _
      _ ≤ #S + #Bset := by have := card_image_le (s := Bset) (f := g); omega
      _ ≤ #F := by omega
