-- Prove2me | solution 1 for NicerEars.TJoin.exists_block_split
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:32:05.985088+00:00
-- url     : https://prove2.me/submissions/44d55490-0991-4c7f-843a-1315be35010b

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

open Finset NicerEars.TJoin

namespace SolBlockSplitAux

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem spanGraph_univ_adj (G : NicerEars.TJoin.Graph V E) (x y : V) :
    (G.spanGraph univ).Adj x y ↔ (∃ e, G.ends e = s(x, y)) ∧ x ≠ y := by
  simp [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj]

theorem sub_adj (G : NicerEars.TJoin.Graph V E) (W : Finset V) (F : Finset E)
    (h : ∀ e ∈ F, ∀ v ∈ G.ends e, v ∈ W) (x y : W) (e : E) (he : e ∈ F)
    (hxy : G.ends e = s(x.1, y.1)) (hne : x ≠ y) :
    ((G.sub W F h).spanGraph univ).Adj x y := by
  rw [spanGraph_univ_adj]
  refine ⟨⟨⟨e, he⟩, ?_⟩, hne⟩
  apply Sym2.map.injective Subtype.val_injective
  rw [G.sub_ends_map W F h ⟨e, he⟩, hxy]
  rfl

/-- Connectivity of the piece `insert v C` for a set `C` closed under adjacency away from `v`. -/
theorem piece_connected (G : NicerEars.TJoin.Graph V E) (hG : G.IsConnected) (v : V)
    (C : Finset V) (hvC : v ∉ C)
    (hcl : ∀ y z, y ≠ v → z ≠ v → (G.spanGraph univ).Adj y z → y ∈ C → z ∈ C)
    (h : ∀ e ∈ univ.filter (fun e => ∀ u ∈ G.ends e, u ∈ insert v C),
      ∀ u ∈ G.ends e, u ∈ insert v C) :
    (G.sub (insert v C) (univ.filter (fun e => ∀ u ∈ G.ends e, u ∈ insert v C)) h).IsConnected := by
  set W := insert v C with hW
  set K := (G.sub W (univ.filter (fun e => ∀ u ∈ G.ends e, u ∈ W)) h).spanGraph univ with hK
  have hv : v ∈ W := mem_insert_self v C
  show K.Connected
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨v, hv⟩, fun w => ?_⟩
  by_contra hw
  let S : Set V := {x | x ∉ W ∨ ∃ hx : x ∈ W, K.Reachable ⟨v, hv⟩ ⟨x, hx⟩}
  have hvS : v ∈ S := Or.inr ⟨hv, SimpleGraph.Reachable.refl _⟩
  have hwS : w.1 ∉ S := by
    rintro (h1 | ⟨hx, hr⟩)
    · exact h1 w.2
    · exact hw hr
  obtain ⟨p⟩ := hG.preconnected v w.1
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart S hvS hwS
  have hadj : (G.spanGraph univ).Adj d.fst d.snd := d.adj
  generalize d.fst = y at hd1 hadj
  generalize d.snd = z at hd2 hadj
  have hzW : z ∈ W := by
    by_contra hz; exact hd2 (Or.inl hz)
  have hzr : ¬ ∃ hx : z ∈ W, K.Reachable ⟨v, hv⟩ ⟨z, hx⟩ := fun hh => hd2 (Or.inr hh)
  have hzv : z ≠ v := by
    rintro rfl; exact hzr ⟨hv, SimpleGraph.Reachable.refl _⟩
  rcases hd1 with hy | ⟨hyW, hyr⟩
  · -- y outside W, z ∈ C
    have hzC : z ∈ C := (mem_insert.mp hzW).resolve_left hzv
    have hyv : y ≠ v := fun h => hy (h ▸ hv)
    exact hy (mem_insert_of_mem (hcl z y hzv hyv hadj.symm hzC))
  · obtain ⟨⟨g, hg⟩, hne⟩ := (spanGraph_univ_adj G y z).mp hadj
    have hgF : g ∈ univ.filter (fun e => ∀ u ∈ G.ends e, u ∈ W) := by
      simp only [mem_filter, mem_univ, true_and]
      intro u hu
      rw [hg, Sym2.mem_iff] at hu
      rcases hu with rfl | rfl
      · exact hyW
      · exact hzW
    have hK' : K.Adj ⟨y, hyW⟩ ⟨z, hzW⟩ :=
      sub_adj G W _ h ⟨y, hyW⟩ ⟨z, hzW⟩ g hgF hg (fun h => hne (congrArg Subtype.val h))
    exact hzr ⟨hzW, hyr.trans hK'.reachable⟩

/-- A connected graph with ≥ 3 vertices, no cut vertex, is 2-edge-connected. -/
theorem twoEC_of_no_cut (G : NicerEars.TJoin.Graph V E) (hG : G.IsConnected)
    (hcard : 3 ≤ Fintype.card V)
    (hpre : ∀ v, ((G.spanGraph univ).induce {w | w ≠ v}).Preconnected) :
    G.IsTwoEdgeConnected := by
  refine ⟨hG, fun e _ => ?_⟩
  obtain ⟨⟨p, q⟩, hpq⟩ := Quot.exists_rep (G.ends e)
  have he : G.ends e = s(p, q) := hpq.symm
  have hpq' : p ≠ q := by
    intro h; apply G.loopless e; rw [he, h]; exact Sym2.mk_isDiag_iff.mpr rfl
  set H := G.spanGraph (univ.erase e)
  -- avoid r ∈ {p, q}
  have avoid : ∀ r, (r = p ∨ r = q) → ∀ x y, x ≠ r → y ≠ r → H.Reachable x y := by
    intro r hr x y hx hy
    let φ : ((G.spanGraph univ).induce {w | w ≠ r}) →g H :=
      { toFun := fun x => x.1
        map_rel' := by
          intro a b hab
          have hab' : (G.spanGraph univ).Adj a.1 b.1 := hab
          obtain ⟨⟨g, hg⟩, hne⟩ := (spanGraph_univ_adj G _ _).mp hab'
          show (G.spanGraph (univ.erase e)).Adj a.1 b.1
          simp only [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj]
          refine ⟨⟨g, ?_, hg⟩, hne⟩
          simp only [coe_erase, coe_univ, Set.mem_diff, Set.mem_univ, Set.mem_singleton_iff,
            true_and]
          rintro rfl
          rw [he] at hg
          have ha : a.1 ≠ r := a.2
          have hb : b.1 ≠ r := b.2
          rcases Sym2.eq_iff.mp hg with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hr with rfl | rfl <;>
            simp_all }
    exact (hpre r ⟨x, hx⟩ ⟨y, hy⟩).map φ
  obtain ⟨c, hc⟩ : ∃ c, c ≠ p ∧ c ≠ q := by
    by_contra hh
    push_neg at hh
    have : (univ : Finset V) ⊆ {p, q} := fun u _ => by
      by_cases hu : u = p
      · simp [hu]
      · simp [hh u hu]
    have := card_le_card this
    rw [card_univ] at this
    have := card_le_two (a := p) (b := q)
    omega
  haveI : Nonempty V := ⟨p⟩
  refine ⟨fun a b => ?_⟩
  by_cases hap : a = p
  · subst hap
    by_cases hbp : b = a
    · subst hbp; rfl
    · exact (avoid q (Or.inr rfl) a c hpq' hc.2).trans (avoid a (Or.inl rfl) c b hc.1 hbp)
  · by_cases hbp : b = p
    · subst hbp
      by_cases haq : a = q
      · subst haq
        exact (avoid b (Or.inl rfl) a c hap hc.1).trans (avoid a (Or.inr rfl) c b hc.2 hpq')
      · exact (avoid q (Or.inr rfl) a c haq hc.2).trans (avoid q (Or.inr rfl) c b hc.2 hpq')
    · exact avoid p (Or.inl rfl) a b hap hbp

end SolBlockSplitAux

open SolBlockSplitAux in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TJoin.Graph V E) (hG : G.IsConnected) (hnot : ¬ G.IsTwoVertexConnected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (v : V) (V₁ V₂ : Finset V) (E₁ E₂ : Finset E),
      V₁ ∪ V₂ = univ ∧ V₁ ∩ V₂ = {v} ∧ E₁ ∪ E₂ = univ ∧ Disjoint E₁ E₂ ∧ V₁ ≠ univ ∧ V₂ ≠ univ ∧
      ∃ (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂),
        (G.sub V₁ E₁ h₁).IsConnected ∧ (G.sub V₂ E₂ h₂).IsConnected := by
  classical
  obtain ⟨v, hv⟩ : ∃ v, ¬ ((G.spanGraph univ).induce {w | w ≠ v}).Preconnected := by
    by_contra hh
    push_neg at hh
    exact hnot ⟨twoEC_of_no_cut G hG hcard hh, hh⟩
  set Gv := (G.spanGraph univ).induce {w | w ≠ v}
  obtain ⟨a, b, hab⟩ : ∃ a b, ¬ Gv.Reachable a b := by
    by_contra hh; push_neg at hh; exact hv hh
  let C : Finset V := univ.filter (fun u => ∃ hu : u ≠ v, Gv.Reachable a ⟨u, hu⟩)
  let C' : Finset V := univ.filter (fun u => u ≠ v ∧ u ∉ C)
  have hmemC : ∀ u (hu : u ≠ v), u ∈ C ↔ Gv.Reachable a ⟨u, hu⟩ := by
    intro u hu
    simp only [C, mem_filter, mem_univ, true_and]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩
  have hvC : v ∉ C := by simp [C]
  have hvC' : v ∉ C' := by simp [C']
  have hadjv : ∀ y z, (hy : y ≠ v) → (hz : z ≠ v) → (G.spanGraph univ).Adj y z →
      Gv.Adj ⟨y, hy⟩ ⟨z, hz⟩ := fun y z hy hz h => h
  have hcl : ∀ y z, y ≠ v → z ≠ v → (G.spanGraph univ).Adj y z → y ∈ C → z ∈ C := by
    intro y z hy hz h hyC
    rw [hmemC y hy] at hyC
    rw [hmemC z hz]
    exact hyC.trans (hadjv y z hy hz h).reachable
  have hcl' : ∀ y z, y ≠ v → z ≠ v → (G.spanGraph univ).Adj y z → y ∈ C' → z ∈ C' := by
    intro y z hy hz h hyC
    simp only [C', mem_filter, mem_univ, true_and] at hyC ⊢
    exact ⟨hz, fun hzC => hyC.2 (hcl z y hz hy h.symm hzC)⟩
  have hC'mem : ∀ u, u ∈ C' ↔ u ≠ v ∧ u ∉ C := by
    intro u; simp [C']
  set V₁ := insert v C
  set V₂ := insert v C'
  set E₁ := univ.filter (fun e => ∀ u ∈ G.ends e, u ∈ V₁)
  set E₂ := univ.filter (fun e => ∀ u ∈ G.ends e, u ∈ V₂)
  have h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁ := fun e he => (mem_filter.mp he).2
  have h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂ := fun e he => (mem_filter.mp he).2
  have haC : a.1 ∈ C := (hmemC a.1 a.2).mpr (SimpleGraph.Reachable.refl _)
  have hbC : b.1 ∉ C := fun h => hab ((hmemC b.1 b.2).mp h)
  refine ⟨v, V₁, V₂, E₁, E₂, ?_, ?_, ?_, ?_, ?_, ?_, h₁, h₂,
    piece_connected G hG v C hvC hcl h₁, piece_connected G hG v C' hvC' hcl' h₂⟩
  · ext u
    simp only [mem_union, mem_insert, mem_univ, iff_true, V₁, V₂, hC'mem]
    tauto
  · ext u
    simp only [mem_inter, mem_insert, mem_singleton, V₁, V₂, hC'mem]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩ <;> tauto
    · rintro rfl; tauto
  · ext e
    simp only [mem_union, mem_univ, iff_true, E₁, E₂, mem_filter, true_and]
    obtain ⟨⟨p, q⟩, hpq⟩ := Quot.exists_rep (G.ends e)
    have he : G.ends e = s(p, q) := hpq.symm
    have hpq' : p ≠ q := by
      intro h; apply G.loopless e; rw [he, h]; exact Sym2.mk_isDiag_iff.mpr rfl
    have hadj : (G.spanGraph univ).Adj p q := (spanGraph_univ_adj G p q).mpr ⟨⟨e, he⟩, hpq'⟩
    rw [he]
    simp only [Sym2.mem_iff, forall_eq_or_imp, forall_eq, V₁, V₂, mem_insert, hC'mem]
    by_cases hp : p = v
    · subst hp
      by_cases hq : q ∈ C
      · left; tauto
      · right; tauto
    · by_cases hq : q = v
      · subst hq
        by_cases hpC : p ∈ C
        · left; tauto
        · right; tauto
      · by_cases hpC : p ∈ C
        · left; exact ⟨Or.inr hpC, Or.inr (hcl p q hp hq hadj hpC)⟩
        · right
          refine ⟨Or.inr ⟨hp, hpC⟩, Or.inr ⟨hq, fun hqC => hpC (hcl q p hq hp hadj.symm hqC)⟩⟩
  · rw [Finset.disjoint_left]
    intro e he1 he2
    simp only [E₁, E₂, mem_filter, mem_univ, true_and] at he1 he2
    obtain ⟨⟨p, q⟩, hpq⟩ := Quot.exists_rep (G.ends e)
    have he : G.ends e = s(p, q) := hpq.symm
    have hpq' : p ≠ q := by
      intro h; apply G.loopless e; rw [he, h]; exact Sym2.mk_isDiag_iff.mpr rfl
    have hp1 := he1 p (by rw [he]; exact Sym2.mem_mk_left p q)
    have hp2 := he2 p (by rw [he]; exact Sym2.mem_mk_left p q)
    have hq1 := he1 q (by rw [he]; exact Sym2.mem_mk_right p q)
    have hq2 := he2 q (by rw [he]; exact Sym2.mem_mk_right p q)
    simp only [V₁, V₂, mem_insert, hC'mem] at hp1 hp2 hq1 hq2
    apply hpq'
    rcases hp1 with h | h <;> rcases hp2 with h' | h' <;> rcases hq1 with k | k <;>
      rcases hq2 with k' | k' <;> first | exact h.trans k.symm | exact h.trans k'.symm | exact h'.trans k.symm | exact h'.trans k'.symm | tauto
  · intro h
    have : b.1 ∈ V₁ := h ▸ mem_univ _
    rcases mem_insert.mp this with h1 | h1
    · exact b.2 h1
    · exact hbC h1
  · intro h
    have : a.1 ∈ V₂ := h ▸ mem_univ _
    rcases mem_insert.mp this with h1 | h1
    · exact a.2 h1
    · exact ((hC'mem _).mp h1).2 haC
