-- Prove2me | solution 1 for NicerEars.TwoEC.theorem_30_twoVertexConnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:52:22.555309+00:00
-- url     : https://prove2.me/submissions/66e64d09-11c4-4a6a-895d-ce3eccb9b4f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Earmuff
import Theorems.Thm_NicerEars_TwoEC_lemma_23
import Theorems.Thm_NicerEars_TwoEC_claim_p23
import Theorems.Thm_NicerEars_TwoEC_theorem_24
import Theorems.Thm_NicerEars_TwoEC_theorem_19
import Theorems.Thm_NicerEars_TwoEC_corollary_21
import Theorems.Thm_NicerEars_TwoEC_tour_to_twoECSS

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

lemma cut_of_ends (G : Graph V E) (W : Finset V) (e : E) (u w : V) (h : G.ends e = s(u, w))
    (hu : u ∈ W) (hw : w ∉ W) : e ∈ G.cut W := (mem_cut G W e).2 ⟨u, hu, w, hw, h⟩

lemma cut_of_ends' (G : Graph V E) (W : Finset V) (e : E) (u w : V) (h : G.ends e = s(u, w))
    (hu : u ∉ W) (hw : w ∈ W) : e ∈ G.cut W :=
  (mem_cut G W e).2 ⟨w, hw, u, hu, h.trans Sym2.eq_swap⟩

lemma ne_of_ends (G : Graph V E) (e e' : E) (p q : Sym2 V) (h : G.ends e = p) (h' : G.ends e' = q)
    (hpq : p ≠ q) : e ≠ e' := by
  rintro rfl; exact hpq (h.symm.trans h')

/-- In a 2-vertex-connected graph, after deleting a vertex `t`, some edge leaves any set `S` that
misses `t` and does not contain every other vertex. -/
lemma escape (G : Graph V E) (hG : G.IsTwoVertexConnected) (t : V) (S : Finset V) (htS : t ∉ S)
    (u : V) (hu : u ∈ S) (c : V) (hc : c ∉ S) (hct : c ≠ t) :
    ∃ s ∈ S, ∃ w, w ∉ S ∧ w ≠ t ∧ (G.spanGraph univ).Adj s w := by
  have hut : u ≠ t := fun h => htS (h ▸ hu)
  obtain ⟨p⟩ := hG.2 t (⟨u, hut⟩ : {w | w ≠ t}) ⟨c, hct⟩
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart {z | z.val ∈ S} (by simpa using hu)
    (by simpa using hc)
  have hadj := d.adj
  rw [SimpleGraph.induce_adj] at hadj
  exact ⟨d.fst.val, hd1, d.snd.val, hd2, d.snd.prop, hadj⟩


lemma exists_not_mem (s : Finset V) (h : #s < Fintype.card V) : ∃ c, c ∉ s := by
  by_contra hc; push Not at hc
  have : s = univ := eq_univ_iff_forall.mpr hc
  rw [this, card_univ] at h; omega

/-- Small cases: 2-vertex-connected graphs with at most three vertices. -/
lemma small_case (G : Graph V E) (hG : G.IsTwoVertexConnected) (hV : Fintype.card V ≤ 3) :
    ∃ F : Finset E, G.IsTwoECSpanning F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 4 / 3 * ∑ e, x e := by
  have hne : Nonempty V := hG.1.1.nonempty
  have hpos : 0 < Fintype.card V := Fintype.card_pos
  interval_cases h : Fintype.card V
  · -- one vertex
    refine ⟨∅, ?_, fun x hx => ?_⟩
    · rw [twoEC_iff_cut]
      intro W hW hWu
      exfalso; apply hWu
      apply eq_univ_of_card
      have := card_le_univ W
      have := hW.card_pos
      omega
    · simp only [card_empty, Nat.cast_zero]
      have := sum_nonneg_of_feasible G x hx
      linarith
  · -- two vertices
    obtain ⟨a, b, hab, huniv⟩ := card_eq_two.1 (show #(univ : Finset V) = 2 by rw [card_univ, h])
    have hmem : ∀ z : V, z = a ∨ z = b := by
      intro z; have := mem_univ z; rw [huniv] at this; simpa using this
    obtain ⟨e₁, -, e₂, -, hne', hc₁, hc₂⟩ := (twoEC_iff_cut G univ).1 hG.1 {a}
      (singleton_nonempty a) (by rw [huniv]; intro hh; have := congrArg (b ∈ ·) hh; simp at this; exact hab this.symm)
    have key : ∀ e ∈ G.cut {a}, ∀ W : Finset V, W.Nonempty → W ≠ univ → e ∈ G.cut W := by
      intro e he W hW hWu
      rw [mem_cut_singleton] at he
      obtain ⟨p, q, hpq, hpq'⟩ := ends_eq G e
      have hends : G.ends e = s(a, b) := by
        rw [hpq'] at he ⊢
        rcases Sym2.mem_iff.1 he with rfl | rfl
        · rcases hmem q with rfl | rfl
          · exact absurd rfl hpq
          · rfl
        · rcases hmem p with rfl | rfl
          · exact absurd rfl hpq
          · exact Sym2.eq_swap
      obtain ⟨w, hw⟩ := hW
      obtain ⟨z, hz⟩ := exists_not_mem W (by
        have := card_le_univ W
        have : #W ≠ Fintype.card V := fun hh => hWu (eq_univ_of_card W hh)
        omega)
      rcases hmem w with rfl | rfl <;> rcases hmem z with rfl | rfl
      · exact absurd hw hz
      · exact cut_of_ends G W e _ _ hends hw hz
      · exact cut_of_ends' G W e _ _ hends hz hw
      · exact absurd hw hz
    refine ⟨{e₁, e₂}, ?_, fun x hx => ?_⟩
    · rw [twoEC_iff_cut]
      intro W hW hWu
      exact ⟨e₁, by simp, e₂, by simp, hne', key e₁ hc₁ W hW hWu, key e₂ hc₂ W hW hWu⟩
    · have h1 := card_le_lp G x hx (by omega)
      have h2 : (#({e₁, e₂} : Finset E) : ℝ) ≤ 2 := by
        exact_mod_cast (card_le_two : #({e₁, e₂} : Finset E) ≤ 2)
      rw [h] at h1
      push_cast at h1
      linarith
  · -- three vertices: a triangle
    obtain ⟨a, b, c, hab, hac, hbc, huniv⟩ :=
      card_eq_three.1 (show #(univ : Finset V) = 3 by rw [card_univ, h])
    have hmem : ∀ z : V, z = a ∨ z = b ∨ z = c := by
      intro z; have := mem_univ z; rw [huniv] at this; simpa using this
    have adj : ∀ u w t : V, u ≠ w → u ≠ t → w ≠ t → (G.spanGraph univ).Adj u w := by
      intro u w t huw hut hwt
      obtain ⟨s, hs, z, hz, hzt, hadj⟩ := escape G hG t {u} (by simpa using hut.symm) u
        (mem_singleton_self u) w (by simpa using huw.symm) hwt
      rw [mem_singleton] at hs hz; subst hs
      have : z = w := by
        rcases hmem z with rfl | rfl | rfl <;> rcases hmem s with rfl | rfl | rfl <;>
          rcases hmem w with rfl | rfl | rfl <;> rcases hmem t with rfl | rfl | rfl <;>
          first | rfl | (exfalso; tauto)
      rwa [this] at hadj
    obtain ⟨-, eab, -, hab'⟩ := (spanGraph_adj G univ a b).1 (adj a b c hab hac hbc)
    obtain ⟨-, ebc, -, hbc'⟩ := (spanGraph_adj G univ b c).1 (adj b c a hbc hab.symm hac.symm)
    obtain ⟨-, eca, -, hca'⟩ := (spanGraph_adj G univ c a).1 (adj c a b hac.symm hbc.symm hab)
    have n1 : eab ≠ ebc := ne_of_ends G _ _ _ _ hab' hbc' (by
      rw [Ne, Sym2.eq_iff]; tauto)
    have n2 : eab ≠ eca := ne_of_ends G _ _ _ _ hab' hca' (by
      rw [Ne, Sym2.eq_iff]; tauto)
    have n3 : ebc ≠ eca := ne_of_ends G _ _ _ _ hbc' hca' (by
      rw [Ne, Sym2.eq_iff]; tauto)
    refine ⟨{eab, ebc, eca}, ?_, fun x hx => ?_⟩
    · rw [twoEC_iff_cut]
      intro W hW hWu
      have hWu' : ¬ (a ∈ W ∧ b ∈ W ∧ c ∈ W) := by
        rintro ⟨h1, h2, h3⟩; apply hWu; apply eq_univ_iff_forall.mpr
        intro z; rcases hmem z with rfl | rfl | rfl <;> assumption
      have hW' : a ∈ W ∨ b ∈ W ∨ c ∈ W := by
        obtain ⟨z, hz⟩ := hW; rcases hmem z with rfl | rfl | rfl <;> tauto
      by_cases ha : a ∈ W <;> by_cases hb : b ∈ W <;> by_cases hc : c ∈ W
      · exact absurd ⟨ha, hb, hc⟩ hWu'
      · exact ⟨ebc, by simp, eca, by simp, n3, cut_of_ends G W _ _ _ hbc' hb hc,
          cut_of_ends' G W _ _ _ hca' hc ha⟩
      · exact ⟨eab, by simp, ebc, by simp, n1, cut_of_ends G W _ _ _ hab' ha hb,
          cut_of_ends' G W _ _ _ hbc' hb hc⟩
      · exact ⟨eab, by simp, eca, by simp, n2, cut_of_ends G W _ _ _ hab' ha hb,
          cut_of_ends' G W _ _ _ hca' hc ha⟩
      · exact ⟨eab, by simp, eca, by simp, n2, cut_of_ends' G W _ _ _ hab' ha hb,
          cut_of_ends G W _ _ _ hca' hc ha⟩
      · exact ⟨eab, by simp, ebc, by simp, n1, cut_of_ends' G W _ _ _ hab' ha hb,
          cut_of_ends G W _ _ _ hbc' hb hc⟩
      · exact ⟨ebc, by simp, eca, by simp, n3, cut_of_ends' G W _ _ _ hbc' hb hc,
          cut_of_ends G W _ _ _ hca' hc ha⟩
      · exfalso; tauto
    · have h1 := card_le_lp G x hx (by omega)
      have h2 : (#({eab, ebc, eca} : Finset E) : ℝ) ≤ 3 := by
        exact_mod_cast (card_le_three : #({eab, ebc, eca} : Finset E) ≤ 3)
      rw [h] at h1
      push_cast at h1
      linarith


lemma inner_of_len_two (G : Graph V E) (P : Ear G) (h : P.len = 2) :
    ∃ v, P.inner = {v} := by
  cases P with
  | mk len hl vert edge link einj vinj =>
    simp only at h; subst h
    refine ⟨vert 1, ?_⟩
    have : (univ.filter (fun i : Fin (2 + 1) => 0 < i.val ∧ i.val < 2)) = {1} := by decide
    simp only [Ear.inner, this, image_singleton]

lemma inner_of_len_three (G : Graph V E) (P : Ear G) (h : P.len = 3) :
    ∃ v₁ v₂, v₁ ≠ v₂ ∧ P.inner = {v₁, v₂} ∧ (G.spanGraph univ).Adj v₁ v₂ := by
  cases P with
  | mk len hl vert edge link einj vinj =>
    simp only at h; subst h
    have hne : vert 1 ≠ vert 2 := by
      intro hh
      rcases vinj 1 2 hh with h' | h'
      · exact absurd h' (by decide)
      · have := congrArg (fun S : Set (Fin 4) => (1 : Fin 4) ∈ S) h'
        simp at this
    refine ⟨vert 1, vert 2, hne, ?_, ?_⟩
    · have : (univ.filter (fun i : Fin (3 + 1) => 0 < i.val ∧ i.val < 3)) = {1, 2} := by decide
      simp only [Ear.inner, this, image_insert, image_singleton]
    · rw [spanGraph_adj]
      exact ⟨hne, edge 1, mem_univ _, link 1⟩

lemma inner_subset_verts (G : Graph V E) (P : Ear G) : P.inner ⊆ P.verts :=
  image_subset_image (subset_univ _)

lemma inner_disjoint (G : Graph V E) (D : EarDecomposition G) (i j : Fin D.k) (hij : i ≠ j) :
    Disjoint (D.ear i).inner (D.ear j).inner := by
  have aux : ∀ i j : Fin D.k, j < i → Disjoint (D.ear i).inner (D.ear j).inner := by
    intro i j hji
    refine (D.attach i).2.2.mono_right ?_
    refine (inner_subset_verts G _).trans ?_
    refine subset_trans ?_ (subset_insert _ _)
    exact subset_biUnion_of_mem (fun j => (D.ear j).verts) (by simpa using hji)
  rcases lt_or_gt_of_ne hij with h | h
  · exact (aux j i h).symm
  · exact aux i j h

/-- Members of the eardrum of a nice ear-decomposition (with `T = ∅`) are the internal vertex
sets of short ears. -/
lemma mem_eardrumOf (G : Graph V E) (D : EarDecomposition G) (f : Finset V)
    (hf : f ∈ D.eardrumOf ∅) : ∃ i, (D.ear i).IsShort ∧ (D.ear i).inner = f := by
  unfold EarDecomposition.eardrumOf at hf
  classical
  simp only [mem_image, mem_filter, mem_univ, true_and] at hf
  obtain ⟨i, hi, rfl⟩ := hf
  exact ⟨i, hi.1, rfl⟩

lemma shape_of_short (G : Graph V E) (P : Ear G) (h : P.IsShort) :
    (∃ v, P.inner = {v}) ∨
      ∃ v₁ v₂, v₁ ≠ v₂ ∧ P.inner = {v₁, v₂} ∧ (G.spanGraph univ).Adj v₁ v₂ := by
  rcases h with h | h
  · exact Or.inl (inner_of_len_two G P h)
  · exact Or.inr (inner_of_len_three G P h)

lemma isEardrum_of_nice (G : Graph V E) (D : EarDecomposition G) (hD : D.IsNice) :
    IsEardrum G (D.eardrumOf ∅) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨i, hs, rfl⟩ := mem_eardrumOf G D f hf
    rcases shape_of_short G _ hs with ⟨v, hv⟩ | ⟨v₁, v₂, hne, hv, -⟩
    · left; rw [hv, card_singleton]
    · right; rw [hv, card_pair hne]
  · intro f hf g hg hfg
    obtain ⟨i, -, rfl⟩ := mem_eardrumOf G D f hf
    obtain ⟨j, -, rfl⟩ := mem_eardrumOf G D g hg
    exact inner_disjoint G D i j (fun h => hfg (h ▸ rfl))
  · intro f hf u hu w hw huw
    obtain ⟨i, hs, rfl⟩ := mem_eardrumOf G D f hf
    rcases shape_of_short G _ hs with ⟨v, hv⟩ | ⟨v₁, v₂, hne, hv, hadj⟩
    · rw [hv, mem_singleton] at hu hw; exact absurd (hu.trans hw.symm) huw
    · rw [hv] at hu hw
      simp only [mem_insert, mem_singleton] at hu hw
      rcases hu with rfl | rfl <;> rcases hw with rfl | rfl
      · exact absurd rfl huw
      · exact hadj
      · exact hadj.symm
      · exact absurd rfl huw
  · intro f hf g hg hfg u hu w hw
    obtain ⟨i, hsi, rfl⟩ := mem_eardrumOf G D f hf
    obtain ⟨j, hsj, rfl⟩ := mem_eardrumOf G D g hg
    exact hD.2.2 i j (fun h => hfg (h ▸ rfl)) hsi hsj u hu w hw

/-- An open 2-path `a - v - b`. -/
lemma exists_path_two (G : Graph V E) (a v b : V) (hav : a ≠ v) (hvb : v ≠ b) (hab : a ≠ b)
    (e₁ e₂ : E) (h₁ : G.ends e₁ = s(a, v)) (h₂ : G.ends e₂ = s(v, b)) :
    ∃ P : Ear G, P.IsOpen ∧ P.inner = {v} := by
  have hne : e₁ ≠ e₂ := ne_of_ends G _ _ _ _ h₁ h₂ (by rw [Ne, Sym2.eq_iff]; tauto)
  let P : Ear G :=
    { len := 2
      len_pos := by norm_num
      vert := ![a, v, b]
      edge := ![e₁, e₂]
      link := by
        intro i; fin_cases i
        · simpa using h₁
        · simpa using h₂
      edge_inj := by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      vert_inj := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm] }
  refine ⟨P, ?_, ?_⟩
  · simpa [Ear.IsOpen, Ear.first, Ear.last, P] using hab
  · have : (univ.filter (fun i : Fin (2 + 1) => 0 < i.val ∧ i.val < 2)) = {1} := by decide
    simp only [Ear.inner, P, this, image_singleton]
    rfl

/-- An open 3-path `a - v₁ - v₂ - b`. -/
lemma exists_path_three (G : Graph V E) (a v₁ v₂ b : V) (h1 : a ≠ v₁) (h2 : a ≠ v₂) (h3 : a ≠ b)
    (h4 : v₁ ≠ v₂) (h5 : v₁ ≠ b) (h6 : v₂ ≠ b)
    (e₁ e₂ e₃ : E) (he₁ : G.ends e₁ = s(a, v₁)) (he₂ : G.ends e₂ = s(v₁, v₂))
    (he₃ : G.ends e₃ = s(v₂, b)) :
    ∃ P : Ear G, P.IsOpen ∧ P.inner = {v₁, v₂} := by
  have n12 : e₁ ≠ e₂ := ne_of_ends G _ _ _ _ he₁ he₂ (by rw [Ne, Sym2.eq_iff]; tauto)
  have n13 : e₁ ≠ e₃ := ne_of_ends G _ _ _ _ he₁ he₃ (by rw [Ne, Sym2.eq_iff]; tauto)
  have n23 : e₂ ≠ e₃ := ne_of_ends G _ _ _ _ he₂ he₃ (by rw [Ne, Sym2.eq_iff]; tauto)
  let P : Ear G :=
    { len := 3
      len_pos := by norm_num
      vert := ![a, v₁, v₂, b]
      edge := ![e₁, e₂, e₃]
      link := by
        intro i; fin_cases i
        · simpa using he₁
        · simpa using he₂
        · simpa using he₃
      edge_inj := by
        intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
      vert_inj := by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all [eq_comm] }
  refine ⟨P, ?_, ?_⟩
  · simpa [Ear.IsOpen, Ear.first, Ear.last, P] using h3
  · have : (univ.filter (fun i : Fin (3 + 1) => 0 < i.val ∧ i.val < 3)) = {1, 2} := by decide
    simp only [Ear.inner, P, this, image_insert, image_singleton]
    rfl


lemma adj_edge (G : Graph V E) (u w : V) (h : (G.spanGraph univ).Adj u w) :
    ∃ e : E, G.ends e = s(u, w) := by
  obtain ⟨-, e, -, he⟩ := (spanGraph_adj G univ u w).1 h; exact ⟨e, he⟩

/-- In a 2-vertex-connected graph with at least four vertices, every member of the eardrum of a
nice ear-decomposition is the inner vertex set of some path (`𝒫_f ≠ ∅`). -/
lemma paths_nonempty (G : Graph V E) (hG : G.IsTwoVertexConnected) (hV : 4 ≤ Fintype.card V)
    (f : Finset V)
    (hf : (∃ v, f = {v}) ∨ ∃ v₁ v₂, v₁ ≠ v₂ ∧ f = {v₁, v₂} ∧ (G.spanGraph univ).Adj v₁ v₂) :
    (PathsThrough G f).Nonempty := by
  rcases hf with ⟨v, rfl⟩ | ⟨v₁, v₂, hne, rfl, hadj⟩
  · obtain ⟨u₀, hu₀⟩ := exists_not_mem {v} (by rw [card_singleton]; omega)
    rw [mem_singleton] at hu₀
    obtain ⟨c₀, hc₀⟩ := exists_not_mem {v, u₀} (by have := card_le_two (a := v) (b := u₀); omega)
    simp only [mem_insert, mem_singleton, not_or] at hc₀
    obtain ⟨s₁, hs₁, w₁, hw₁, -, hadj₁⟩ := escape G hG u₀ {v} (by simpa [eq_comm] using hu₀) v
      (mem_singleton_self v) c₀ (by simpa using hc₀.1) hc₀.2
    rw [mem_singleton] at hs₁ hw₁; subst hs₁
    obtain ⟨c₁, hc₁⟩ := exists_not_mem {s₁, w₁} (by have := card_le_two (a := s₁) (b := w₁); omega)
    simp only [mem_insert, mem_singleton, not_or] at hc₁
    obtain ⟨s₂, hs₂, w₂, hw₂, hw₂₁, hadj₂⟩ := escape G hG w₁ {s₁} (by simpa [eq_comm] using hw₁) s₁
      (mem_singleton_self _) c₁ (by simpa using hc₁.1) hc₁.2
    rw [mem_singleton] at hs₂ hw₂; subst hs₂
    obtain ⟨e₁, he₁⟩ := adj_edge G _ _ hadj₁.symm
    obtain ⟨e₂, he₂⟩ := adj_edge G _ _ hadj₂
    obtain ⟨P, hP, hPi⟩ := exists_path_two G w₁ s₂ w₂ hw₁ (fun h => hw₂ h.symm)
      (Ne.symm hw₂₁) e₁ e₂ he₁ he₂
    exact ⟨P, hP, hPi⟩
  · -- the 3-ear case
    obtain ⟨c₀, hc₀⟩ := exists_not_mem {v₁, v₂} (by have := card_le_two (a := v₁) (b := v₂); omega)
    simp only [mem_insert, mem_singleton, not_or] at hc₀
    obtain ⟨s₁, hs₁, a₁, ha₁, ha₁v₂, hadj₁⟩ := escape G hG v₂ {v₁} (by simpa [eq_comm] using hne)
      v₁ (mem_singleton_self _) c₀ (by simpa using hc₀.1) hc₀.2
    rw [mem_singleton] at hs₁ ha₁; subst hs₁
    obtain ⟨s₂, hs₂, b₁, hb₁, hb₁v₁, hadj₂⟩ := escape G hG s₁ {v₂} (by simpa using hne) v₂
      (mem_singleton_self _) c₀ (by simpa using hc₀.2) hc₀.1
    rw [mem_singleton] at hs₂ hb₁; subst hs₂
    -- helper to finish from two distinct outer neighbours
    have finish : ∀ a b : V, a ≠ s₁ → a ≠ s₂ → b ≠ s₁ → b ≠ s₂ → a ≠ b →
        (G.spanGraph univ).Adj a s₁ → (G.spanGraph univ).Adj s₂ b →
        (PathsThrough G {s₁, s₂}).Nonempty := by
      intro a b h1 h2 h3 h4 h5 ha hb
      obtain ⟨e₁, he₁⟩ := adj_edge G _ _ ha
      obtain ⟨e₂, he₂⟩ := adj_edge G _ _ hadj
      obtain ⟨e₃, he₃⟩ := adj_edge G _ _ hb
      obtain ⟨P, hP, hPi⟩ := exists_path_three G a s₁ s₂ b h1 h2 h5 hne
        (fun h => h3 h.symm) (fun h => h4 h.symm) e₁ e₂ e₃ he₁ he₂ he₃
      exact ⟨P, hP, hPi⟩
    by_cases hab : a₁ = b₁
    · subst hab
      obtain ⟨c₂, hc₂⟩ := exists_not_mem {s₁, s₂, a₁} (by
        have := card_le_three (a := s₁) (b := s₂) (c := a₁); omega)
      simp only [mem_insert, mem_singleton, not_or] at hc₂
      obtain ⟨s, hs, w, hw, hwa, hadjw⟩ := escape G hG a₁ {s₁, s₂}
        (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨ha₁, ha₁v₂⟩)
        s₁ (by simp) c₂ (by simp only [mem_insert, mem_singleton, not_or]; exact ⟨hc₂.1, hc₂.2.1⟩)
        hc₂.2.2
      simp only [mem_insert, mem_singleton, not_or] at hs hw
      rcases hs with hs | hs <;> rw [hs] at hadjw
      · exact finish w a₁ hw.1 hw.2 ha₁ ha₁v₂ hwa hadjw.symm hadj₂
      · exact finish a₁ w ha₁ ha₁v₂ hw.1 hw.2 (Ne.symm hwa) hadj₁.symm hadjw
    · exact finish a₁ b₁ ha₁ ha₁v₂ hb₁v₁ hb₁ hab hadj₁.symm hadj₂

lemma main_large (G : Graph V E) (hG : G.IsTwoVertexConnected) (hV : 4 ≤ Fintype.card V) :
    ∃ F : Finset E, G.IsTwoECSpanning F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 4 / 3 * ∑ e, x e := by
  obtain ⟨D, hnice, hmax⟩ := lemma_23 G hG ∅ (by simp)
  obtain ⟨hA, hAcard⟩ := claim_p23 G D hnice
  obtain ⟨Ft, hFt, hFtcard⟩ := theorem_24 G ∅ (by simp) D hnice hmax
  obtain ⟨B, hB, hBcard⟩ := tour_to_twoECSS G hG.1 Ft hFt
  have hM := isEardrum_of_nice G D hnice
  have hP : ∀ f ∈ D.eardrumOf ∅, (PathsThrough G f).Nonempty := by
    intro f hf
    obtain ⟨i, hs, rfl⟩ := mem_eardrumOf G D f hf
    exact paths_nonempty G hG hV _ (shape_of_short G _ hs)
  have h21 := (corollary_21 G hG.1 _ hM hP).1
  have h19 := (theorem_19 G hG.1).1
  have hBr : (#B : ℝ) ≤ #Ft := by exact_mod_cast hBcard
  by_cases hle : #D.nontrivialEdges ≤ #B
  · refine ⟨D.nontrivialEdges, hA, fun x hx => ?_⟩
    have := h21 x hx; have := h19 x hx
    have : (#D.nontrivialEdges : ℝ) ≤ #B := by exact_mod_cast hle
    linarith
  · refine ⟨B, hB, fun x hx => ?_⟩
    have := h21 x hx; have := h19 x hx
    have : (#B : ℝ) ≤ #D.nontrivialEdges := by exact_mod_cast (le_of_lt (not_le.1 hle))
    linarith

end NicerEars.TwoEC.Aux30

open Finset in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : NicerEars.TwoEC.Graph V E) (hG : G.IsTwoVertexConnected) :
    ∃ F : Finset E, G.IsTwoECSpanning F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 4 / 3 * ∑ e, x e := by
  by_cases hV : 4 ≤ Fintype.card V
  · exact NicerEars.TwoEC.Aux30.main_large G hG hV
  · exact NicerEars.TwoEC.Aux30.small_case G hG (by omega)
