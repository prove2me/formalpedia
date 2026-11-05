-- Prove2me | solution 1 for NicerEars.TwoEC.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:06:27.858187+00:00
-- url     : https://prove2.me/submissions/e9212748-cf41-40fe-a6ed-7cafa4c7647f

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

/-- Summing the singleton cut constraints: `x(E) ≥ |V|`. -/
lemma card_le_lp (G : Graph V E) (x : E → ℝ) (hx : G.LPFeasible x) (hV : 2 ≤ Fintype.card V) :
    (Fintype.card V : ℝ) ≤ ∑ e, x e := by
  have h1 : ∀ v : V, 2 ≤ ∑ e ∈ G.cut {v}, x e := by
    intro v
    refine hx.2 {v} (singleton_nonempty v) ?_
    intro h
    have := congrArg Finset.card h
    rw [card_singleton, card_univ] at this
    omega
  have hsum : ∑ v : V, ∑ e ∈ G.cut {v}, x e = ∑ e, 2 * x e := by
    have hc : ∀ v : V, G.cut {v} = univ.filter (fun e => v ∈ G.ends e) := by
      intro v; ext e; simp [mem_cut_singleton]
    simp_rw [hc, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const]
    obtain ⟨a, b, hab, h⟩ := ends_eq G e
    have : univ.filter (fun v => v ∈ G.ends e) = {a, b} := by
      ext v; simp [h]
    rw [this, card_pair hab]
    simp
  have : (Fintype.card V : ℝ) * 2 ≤ ∑ v : V, ∑ e ∈ G.cut {v}, x e := by
    calc (Fintype.card V : ℝ) * 2 = ∑ _v : V, (2 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun v _ => h1 v)
  rw [hsum, ← Finset.mul_sum] at this
  linarith

lemma sum_nonneg_of_feasible (G : Graph V E) (x : E → ℝ) (hx : G.LPFeasible x) :
    0 ≤ ∑ e, x e := Finset.sum_nonneg (fun e _ => hx.1 e)


end NicerEars.TwoEC.Aux30

open Finset NicerEars.TwoEC.Aux30 in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TwoEC.Graph V E) (hG : G.IsConnected) (hV : 2 ≤ Fintype.card V) :
    (G.OPT2EC : ℝ) ≤ G.OPTTour ∧ G.lpValue ≤ G.OPT2EC ∧ (Fintype.card V : ℝ) ≤ G.lpValue := by
  have hne : Nonempty V := hG.nonempty
  -- the simple graph spanned by a multi-subgraph of 2G
  have hspan : ∀ F : Finset (E × Fin 2),
      G.double.spanGraph F = G.spanGraph (F.image Prod.fst) := by
    intro F
    ext u w
    rw [spanGraph_adj, spanGraph_adj]
    simp only [mem_image, NicerEars.TwoEC.Graph.double]
    constructor
    · rintro ⟨huw, p, hp, he⟩; exact ⟨huw, p.1, ⟨p, hp, rfl⟩, he⟩
    · rintro ⟨huw, e, ⟨p, hp, rfl⟩, he⟩; exact ⟨huw, p, hp, he⟩
  have hcut2 : ∀ (W : Finset V) (p : E × Fin 2), p ∈ G.double.cut W ↔ p.1 ∈ G.cut W := by
    intro W p; rw [mem_cut, mem_cut]; rfl
  -- (i) a minimum tour is 2-edge-connected in 2G
  have htour_ne : {n | ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin ∅ F ∧ #F = n}.Nonempty := by
    refine ⟨_, univ, ⟨?_, ?_⟩, rfl⟩
    · intro v
      simp only [Finset.notMem_empty, iff_false, Nat.not_odd_iff_even]
      have : (univ : Finset (E × Fin 2)).filter (fun p => v ∈ G.double.ends p) =
          (univ.filter (fun e => v ∈ G.ends e)) ×ˢ (univ : Finset (Fin 2)) := by
        ext ⟨e, i⟩
        simp only [mem_filter, mem_product, mem_univ, true_and, and_true]
        rfl
      rw [this, card_product, Finset.card_univ, Fintype.card_fin]
      exact ⟨_, (mul_two _)⟩
    · rw [hspan]
      have : (univ : Finset (E × Fin 2)).image Prod.fst = univ := by
        ext e; simp only [mem_image, mem_univ, true_and, iff_true]; exact ⟨(e, 0), rfl⟩
      rw [this]; exact hG
  obtain ⟨F₀, hF₀, hF₀c⟩ := Nat.sInf_mem htour_ne
  have hF₀2 : G.double.IsTwoECSpanning F₀ := by
    rw [twoEC_iff_cut]
    intro W hW hWu
    obtain ⟨hTJ, hconn⟩ := hF₀
    obtain ⟨p, hp, hpc⟩ := (connected_iff_cut _ _).1 hconn W hW hWu
    have heven : ∀ v, Even #(F₀.filter (fun p => v ∈ G.double.ends p)) := by
      intro v; rw [← Nat.not_odd_iff_even]; intro h; have := (hTJ v).1 h; simp at this
    have hev := even_cut G.double F₀ heven W
    have hpos : 0 < #(F₀.filter (fun p => p ∈ G.double.cut W)) :=
      card_pos.2 ⟨p, mem_filter.2 ⟨hp, hpc⟩⟩
    have h1 : 1 < #(F₀.filter (fun p => p ∈ G.double.cut W)) := by
      rcases hev with ⟨k, hk⟩; omega
    obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.1 h1
    rw [mem_filter] at ha hb
    exact ⟨a, ha.1, b, hb.1, hab, ha.2, hb.2⟩
  have hi : G.OPT2EC ≤ G.OPTTour := by
    unfold NicerEars.TwoEC.Graph.OPTTour NicerEars.TwoEC.Graph.OPT
    rw [← hF₀c]
    exact Nat.sInf_le ⟨F₀, hF₀2, rfl⟩
  -- (ii) a minimum 2ECSS of 2G gives a feasible LP point
  have h2ec_ne : {n | ∃ F : Finset (E × Fin 2), G.double.IsTwoECSpanning F ∧ #F = n}.Nonempty :=
    ⟨_, F₀, hF₀2, rfl⟩
  obtain ⟨F₁, hF₁, hF₁c⟩ := Nat.sInf_mem h2ec_ne
  let x : E → ℝ := fun e => (#(F₁.filter (fun p => p.1 = e)) : ℝ)
  have hsumS : ∀ S : Finset E, ∑ e ∈ S, x e = (#(F₁.filter (fun p => p.1 ∈ S)) : ℝ) := by
    intro S
    simp only [x]
    rw [← Nat.cast_sum]
    congr 1
    rw [card_eq_sum_card_fiberwise (f := Prod.fst) (s := F₁.filter (fun p => p.1 ∈ S)) (t := S)
      (fun p hp => (mem_filter.1 hp).2)]
    refine sum_congr rfl (fun e he => ?_)
    congr 1
    ext p; simp only [mem_filter]
    constructor
    · rintro ⟨hp, rfl⟩; exact ⟨⟨hp, he⟩, rfl⟩
    · rintro ⟨⟨hp, -⟩, h⟩; exact ⟨hp, h⟩
  have hxfeas : G.LPFeasible x := by
    refine ⟨fun e => Nat.cast_nonneg _, fun W hW hWu => ?_⟩
    rw [hsumS]
    rw [twoEC_iff_cut] at hF₁
    obtain ⟨a, ha, b, hb, hab, hac, hbc⟩ := hF₁ W hW hWu
    have : 1 < #(F₁.filter (fun p => p.1 ∈ G.cut W)) :=
      one_lt_card.2 ⟨a, mem_filter.2 ⟨ha, (hcut2 W a).1 hac⟩, b,
        mem_filter.2 ⟨hb, (hcut2 W b).1 hbc⟩, hab⟩
    have : (2 : ℝ) ≤ #(F₁.filter (fun p => p.1 ∈ G.cut W)) := by exact_mod_cast this
    exact this
  have hxsum : ∑ e, x e = (G.OPT2EC : ℝ) := by
    rw [hsumS]
    unfold NicerEars.TwoEC.Graph.OPT2EC
    rw [← hF₁c]
    congr 2
    ext p; simp
  have hbdd : BddBelow ((fun x : E → ℝ => ∑ e, x e) '' {x | G.LPFeasible x}) :=
    ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact Finset.sum_nonneg (fun e _ => hy.1 e)⟩
  have hii : G.lpValue ≤ G.OPT2EC := by
    unfold NicerEars.TwoEC.Graph.lpValue
    rw [← hxsum]
    exact csInf_le hbdd ⟨x, hxfeas, rfl⟩
  have hiii : (Fintype.card V : ℝ) ≤ G.lpValue := by
    unfold NicerEars.TwoEC.Graph.lpValue
    refine le_csInf ⟨_, ⟨x, hxfeas, rfl⟩⟩ ?_
    rintro _ ⟨y, hy, rfl⟩
    exact card_le_lp G y hy hV
  exact ⟨by exact_mod_cast hi, hii, hiii⟩
