-- Prove2me | solution 1 for NicerEars.TJoin.proposition_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:48:46.585628+00:00
-- url     : https://prove2.me/submissions/ee25dc80-84b2-4231-a46c-ae14077d7716

import Mathlib
import Definitions.Def_NicerEars_TJoin_Setting

open Finset NicerEars.TJoin

namespace SolProp4Aux

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem ends_rep (G : NicerEars.TJoin.Graph V E) (e : E) :
    ∃ a b, a ≠ b ∧ G.ends e = s(a, b) := by
  obtain ⟨⟨p, q⟩, hpq⟩ := Quot.exists_rep (G.ends e)
  have he : G.ends e = s(p, q) := hpq.symm
  refine ⟨p, q, ?_, he⟩
  intro h; apply G.loopless e; rw [he, h]; exact Sym2.mk_isDiag_iff.mpr rfl

theorem sub_ends_iff (G : NicerEars.TJoin.Graph V E) (W : Finset V) (F : Finset E)
    (h : ∀ e ∈ F, ∀ u ∈ G.ends e, u ∈ W) (e : F) (a b : W) :
    (G.sub W F h).ends e = s(a, b) ↔ G.ends e.1 = s(a.1, b.1) := by
  rw [← G.sub_ends_map W F h e]
  constructor
  · intro h'; rw [h']; rfl
  · intro h'
    apply Sym2.map.injective Subtype.val_injective
    rw [h']; rfl

theorem mem_sub_ends (G : NicerEars.TJoin.Graph V E) (W : Finset V) (F : Finset E)
    (h : ∀ e ∈ F, ∀ u ∈ G.ends e, u ∈ W) (e : F) (a : W) :
    a ∈ (G.sub W F h).ends e ↔ a.1 ∈ G.ends e.1 := by
  rw [← G.sub_ends_map W F h e, Sym2.mem_map]
  constructor
  · intro h'; exact ⟨a, h', rfl⟩
  · rintro ⟨b, hb, hba⟩
    rwa [← Subtype.ext hba]

theorem double_adj {E' : Type} (G : NicerEars.TJoin.Graph V E') (F : Finset (E' × Fin 2)) (x y : V) :
    (G.double.spanGraph F).Adj x y ↔ (∃ p ∈ F, G.ends p.1 = s(x, y)) ∧ x ≠ y := by
  simp [NicerEars.TJoin.Graph.spanGraph, SimpleGraph.fromEdgeSet_adj, NicerEars.TJoin.Graph.double]

/-- lifting copies of a side's edges -/
def ι {F : Finset E} : F × Fin 2 ↪ E × Fin 2 :=
  ⟨fun p => (p.1.1, p.2), fun p q h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) h.2⟩

@[simp] theorem ι_apply {F : Finset E} (p : F × Fin 2) : (ι p : E × Fin 2) = (p.1.1, p.2) := rfl

/-- restriction of a multi-subgraph to a side -/
def R (F : Finset E) (K : Finset (E × Fin 2)) : Finset (F × Fin 2) :=
  univ.filter (fun p => ι p ∈ K)

theorem map_R (F : Finset E) (K : Finset (E × Fin 2)) :
    (R F K).map ι = K.filter (fun p => p.1 ∈ F) := by
  ext ⟨e, i⟩
  simp only [R, mem_map, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨e', he'⟩, j⟩, hK, h⟩
    simp only [ι_apply, Prod.mk.injEq] at h hK
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hK, he'⟩
  · rintro ⟨hK, he⟩
    exact ⟨(⟨e, he⟩, i), hK, rfl⟩

theorem R_erase (F : Finset E) (K : Finset (E × Fin 2)) (p : F × Fin 2) :
    R F (K.erase (ι p)) = (R F K).erase p := by
  ext q
  simp only [R, mem_filter, mem_univ, true_and, mem_erase]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (h ▸ rfl), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 (ι.injective h), h2⟩

theorem R_map_self (F : Finset E) (A : Finset (F × Fin 2)) : R F (A.map ι) = A := by
  ext q; simp [R]

theorem R_map_other (F F' : Finset E) (hd : Disjoint F F') (A : Finset (F' × Fin 2)) :
    R F (A.map ι) = ∅ := by
  ext q
  simp only [R, mem_filter, mem_univ, true_and, mem_map, notMem_empty, iff_false, not_exists,
    not_and]
  intro a _ h
  simp only [ι_apply, Prod.mk.injEq] at h
  exact Finset.disjoint_left.mp hd q.1.2 (h.1 ▸ a.1.2)

/-- union of the lifts is connected -/
theorem union_connected (G : NicerEars.TJoin.Graph V E) (v : V) (V₁ V₂ : Finset V)
    (E₁ E₂ : Finset E) (hV : V₁ ∪ V₂ = univ) (hv₁ : v ∈ V₁) (hv₂ : v ∈ V₂)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂)
    (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2))
    (hF₁ : ((G.sub V₁ E₁ h₁).double.spanGraph F₁).Connected)
    (hF₂ : ((G.sub V₂ E₂ h₂).double.spanGraph F₂).Connected) :
    (G.double.spanGraph (F₁.map ι ∪ F₂.map ι)).Connected := by
  set K := G.double.spanGraph (F₁.map ι ∪ F₂.map ι)
  have side : ∀ (W : Finset V) (F : Finset E) (h : ∀ e ∈ F, ∀ u ∈ G.ends e, u ∈ W)
      (A : Finset (F × Fin 2)), A.map ι ⊆ F₁.map ι ∪ F₂.map ι →
      ((G.sub W F h).double.spanGraph A).Connected → ∀ (hv : v ∈ W) (u : V) (hu : u ∈ W),
      K.Reachable v u := by
    intro W F h A hA hc hv u hu
    let φ : (G.sub W F h).double.spanGraph A →g K :=
      { toFun := fun x => x.1
        map_rel' := by
          intro x y hxy
          rw [double_adj] at hxy ⊢
          obtain ⟨⟨p, hp, hpe⟩, hne⟩ := hxy
          refine ⟨⟨ι p, hA (mem_map_of_mem _ hp), ?_⟩, fun h => hne (Subtype.ext h)⟩
          exact (sub_ends_iff G W F h p.1 x y).mp hpe }
    exact (hc.preconnected ⟨v, hv⟩ ⟨u, hu⟩).map φ
  haveI : Nonempty V := ⟨v⟩
  refine ⟨fun a b => ?_⟩
  have hr : ∀ u, K.Reachable v u := by
    intro u
    have : u ∈ V₁ ∪ V₂ := hV ▸ mem_univ u
    rcases mem_union.mp this with hu | hu
    · exact side V₁ E₁ h₁ F₁ subset_union_left hF₁ hv₁ u hu
    · exact side V₂ E₂ h₂ F₂ subset_union_right hF₂ hv₂ u hu
  exact (hr a).symm.trans (hr b)

/-- restriction of a connected multi-subgraph to a side is connected -/
theorem restrict_connected (G : NicerEars.TJoin.Graph V E) (v : V) (V₁ V₂ : Finset V)
    (E₁ E₂ : Finset E) (hV₁₂ : V₁ ∩ V₂ = {v}) (hE : E₁ ∪ E₂ = univ) (hv₁ : v ∈ V₁)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂)
    (K : Finset (E × Fin 2)) (hK : (G.double.spanGraph K).Connected) :
    ((G.sub V₁ E₁ h₁).double.spanGraph (R E₁ K)).Connected := by
  set K₁ := (G.sub V₁ E₁ h₁).double.spanGraph (R E₁ K)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨v, hv₁⟩, fun w => ?_⟩
  by_contra hw
  let S : Set V := {x | x ∉ V₁ ∨ ∃ hx : x ∈ V₁, K₁.Reachable ⟨v, hv₁⟩ ⟨x, hx⟩}
  have hvS : v ∈ S := Or.inr ⟨hv₁, SimpleGraph.Reachable.refl _⟩
  have hwS : w.1 ∉ S := by
    rintro (h1 | ⟨hx, hr⟩)
    · exact h1 w.2
    · exact hw hr
  obtain ⟨p⟩ := hK.preconnected v w.1
  obtain ⟨d, -, hd1, hd2⟩ := p.exists_boundary_dart S hvS hwS
  have hadj := d.adj
  generalize d.fst = y at hd1 hadj
  generalize d.snd = z at hd2 hadj
  rw [double_adj] at hadj
  obtain ⟨⟨q, hq, hqe⟩, hne⟩ := hadj
  have hzW : z ∈ V₁ := by
    by_contra hz; exact hd2 (Or.inl hz)
  have hzr : ¬ ∃ hx : z ∈ V₁, K₁.Reachable ⟨v, hv₁⟩ ⟨z, hx⟩ := fun hh => hd2 (Or.inr hh)
  have hzv : z ≠ v := by
    rintro rfl; exact hzr ⟨hv₁, SimpleGraph.Reachable.refl _⟩
  have hzmem : z ∈ G.ends q.1 := by rw [hqe]; exact Sym2.mem_mk_right y z
  have hymem : y ∈ G.ends q.1 := by rw [hqe]; exact Sym2.mem_mk_left y z
  have hqE₁ : q.1 ∈ E₁ := by
    have : q.1 ∈ E₁ ∪ E₂ := hE ▸ mem_univ _
    rcases mem_union.mp this with h | h
    · exact h
    · exfalso
      have : z ∈ V₁ ∩ V₂ := mem_inter.mpr ⟨hzW, h₂ _ h z hzmem⟩
      rw [hV₁₂, mem_singleton] at this
      exact hzv this
  have hyW : y ∈ V₁ := h₁ _ hqE₁ y hymem
  rcases hd1 with hy | ⟨hyW', hyr⟩
  · exact hy hyW
  · have hK' : K₁.Adj ⟨y, hyW'⟩ ⟨z, hzW⟩ := by
      rw [double_adj]
      refine ⟨⟨(⟨q.1, hqE₁⟩, q.2), ?_, ?_⟩, fun h => hne (congrArg Subtype.val h)⟩
      · simp only [R, mem_filter, mem_univ, true_and]; exact hq
      · exact (sub_ends_iff G V₁ E₁ h₁ ⟨q.1, hqE₁⟩ ⟨y, hyW'⟩ ⟨z, hzW⟩).mpr hqe
    exact hzr ⟨hzW, hyr.trans hK'.reachable⟩


/-- handshake lemma modulo 2 -/
theorem handshake {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
    (G : NicerEars.TJoin.Graph V' E') (K : Finset (E' × Fin 2)) :
    ∑ u : V', ((#(K.filter (fun p => u ∈ G.double.ends p)) : ℕ) : ZMod 2) = 0 := by
  rw [← Nat.cast_sum]
  have : ∑ u : V', #(K.filter (fun p => u ∈ G.double.ends p)) = ∑ p ∈ K, 2 := by
    simp_rw [card_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    obtain ⟨a, b, hab, he⟩ := ends_rep G p.1
    rw [← card_filter]
    have : (univ.filter (fun u : V' => u ∈ G.double.ends p)) = {a, b} := by
      ext u; simp [NicerEars.TJoin.Graph.double, he, Sym2.mem_iff]
    rw [this, card_pair hab]
  rw [this, sum_const, smul_eq_mul, Nat.cast_mul]
  have h2 : ((2 : ℕ) : ZMod 2) = 0 := by decide
  rw [h2, mul_zero]

/-- parity at the cut vertex from the handshake lemma -/
theorem parity_at {V' : Type} [Fintype V'] [DecidableEq V'] (d : V' → ℕ) (T' : Finset V')
    (hT' : Even #T') (hs : ∑ u, ((d u : ℕ) : ZMod 2) = 0) (w : V')
    (hoff : ∀ u, u ≠ w → (Odd (d u) ↔ u ∈ T')) : Odd (d w) ↔ w ∈ T' := by
  have hind : ∀ u, u ≠ w → ((d u : ℕ) : ZMod 2) = if u ∈ T' then 1 else 0 := by
    intro u hu
    by_cases h : u ∈ T'
    · rw [if_pos h]; exact ZMod.natCast_eq_one_iff_odd.mpr ((hoff u hu).mpr h)
    · rw [if_neg h]
      apply ZMod.natCast_eq_zero_iff_even.mpr
      rcases Nat.even_or_odd (d u) with h' | h'
      · exact h'
      · exact absurd ((hoff u hu).mp h') h
  have hT0 : ∑ u, (if u ∈ T' then (1 : ZMod 2) else 0) = 0 := by
    rw [sum_boole, filter_mem_eq_inter, univ_inter]
    exact ZMod.natCast_eq_zero_iff_even.mpr hT'
  have hdiff : ∑ u, (((d u : ℕ) : ZMod 2) - if u ∈ T' then 1 else 0) = 0 := by
    rw [sum_sub_distrib, hs, hT0, sub_zero]
  rw [← sum_erase_add _ _ (mem_univ w)] at hdiff
  have hrest : ∑ u ∈ univ.erase w, (((d u : ℕ) : ZMod 2) - if u ∈ T' then 1 else 0) = 0 := by
    apply sum_eq_zero
    intro u hu
    rw [hind u (ne_of_mem_erase hu), sub_self]
  rw [hrest, zero_add, sub_eq_zero] at hdiff
  by_cases h : w ∈ T'
  · rw [if_pos h] at hdiff
    exact ⟨fun _ => h, fun _ => ZMod.natCast_eq_one_iff_odd.mp hdiff⟩
  · rw [if_neg h] at hdiff
    have := ZMod.natCast_eq_zero_iff_even.mp hdiff
    exact ⟨fun ho => absurd this (Nat.not_even_iff_odd.mpr ho), fun h' => absurd h' h⟩

theorem deg_sub (G : NicerEars.TJoin.Graph V E) (W : Finset V) (F : Finset E)
    (h : ∀ e ∈ F, ∀ u ∈ G.ends e, u ∈ W) (A : Finset (F × Fin 2)) (u : W) :
    #(A.filter (fun p => u ∈ (G.sub W F h).double.ends p)) =
      #((A.map ι).filter (fun p => u.1 ∈ G.double.ends p)) := by
  rw [filter_map, card_map]
  congr 1
  apply filter_congr
  intro p _
  simp only [NicerEars.TJoin.Graph.double, Function.comp, ι_apply]
  exact mem_sub_ends G W F h p.1 u

theorem T_side_mem (V₁ : Finset V) (v : V) (T : Finset V) (T₁ : Finset V₁)
    (hT₁ : T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁))
    (u : V₁) (hu : u.1 ≠ v) : u ∈ T₁ ↔ u.1 ∈ T := by
  have : u ∈ T₁ ↔ u.1 ∈ T₁.map (Function.Embedding.subtype _) := by
    simp
  rw [this]
  rcases hT₁ with h | h <;> rw [h] <;> simp [hu, u.2]

/-- restriction of a T-join is a T₁-join -/
theorem restrict_tjoin (G : NicerEars.TJoin.Graph V E) (v : V) (V₁ V₂ : Finset V)
    (E₁ E₂ : Finset E) (hV₁₂ : V₁ ∩ V₂ = {v}) (hE : E₁ ∪ E₂ = univ)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂)
    (T : Finset V) (T₁ : Finset V₁)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁)))
    (K : Finset (E × Fin 2)) (hK : G.double.IsTJoin T K) :
    (G.sub V₁ E₁ h₁).double.IsTJoin T₁ (R E₁ K) := by
  have hv₁ : v ∈ V₁ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).1
  have hoff : ∀ u : V₁, u ≠ ⟨v, hv₁⟩ →
      (Odd #((R E₁ K).filter (fun p => u ∈ (G.sub V₁ E₁ h₁).double.ends p)) ↔ u ∈ T₁) := by
    intro u hu
    have hu' : u.1 ≠ v := fun h => hu (Subtype.ext h)
    rw [deg_sub, map_R, T_side_mem V₁ v T T₁ hT₁.2 u hu', ← hK u.1, filter_filter]
    have : K.filter (fun p => p.1 ∈ E₁ ∧ u.1 ∈ G.double.ends p) =
        K.filter (fun p => u.1 ∈ G.double.ends p) := by
      apply filter_congr
      intro p _
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        have : p.1 ∈ E₁ ∪ E₂ := hE ▸ mem_univ _
        rcases mem_union.mp this with h' | h'
        · exact h'
        · exfalso
          have hu2 := h₂ _ h' u.1 h
          have : u.1 ∈ V₁ ∩ V₂ := mem_inter.mpr ⟨u.2, hu2⟩
          rw [hV₁₂, mem_singleton] at this
          exact hu' this
    rw [this]
  intro u
  by_cases hu : u = ⟨v, hv₁⟩
  · subst hu
    exact parity_at _ T₁ hT₁.1 (handshake _ _) _ hoff
  · exact hoff u hu


theorem T_side_v (V₁ : Finset V) (v : V) (hv₁ : v ∈ V₁) (T : Finset V) (T₁ : Finset V₁)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁))) :
    (⟨v, hv₁⟩ : V₁) ∈ T₁ ↔ Odd #((T ∩ V₁).erase v) := by
  have hmem : (⟨v, hv₁⟩ : V₁) ∈ T₁ ↔ v ∈ T₁.map (Function.Embedding.subtype _) :=
    (Finset.mem_map' (Function.Embedding.subtype _)).symm
  have hcard : #T₁ = #(T₁.map (Function.Embedding.subtype _)) := (card_map _).symm
  rcases hT₁ with ⟨he, h | h⟩
  · rw [hmem, h]
    rw [hcard, h] at he
    simp only [mem_erase, ne_eq, not_true_eq_false, false_and, false_iff]
    exact Nat.not_odd_iff_even.mpr he
  · rw [hmem, h]
    rw [hcard, h] at he
    simp only [mem_insert, true_or, true_iff]
    have hpar : #(insert v (T ∩ V₁)) = #((T ∩ V₁).erase v) + 1 := by
      by_cases hvT : v ∈ T ∩ V₁
      · rw [insert_eq_of_mem hvT, card_erase_add_one hvT]
      · rw [card_insert_of_notMem hvT, erase_eq_of_notMem hvT]
    rw [hpar] at he
    exact Nat.even_add_one.mp he |> Nat.not_even_iff_odd.mp

theorem card_T_split (v : V) (V₁ V₂ : Finset V) (hV : V₁ ∪ V₂ = univ) (hV₁₂ : V₁ ∩ V₂ = {v})
    (T : Finset V) :
    #T = #((T ∩ V₁).erase v) + #((T ∩ V₂).erase v) + (if v ∈ T then 1 else 0) := by
  have hu : (T ∩ V₁).erase v ∪ (T ∩ V₂).erase v = T.erase v := by
    ext u
    simp only [mem_union, mem_erase, mem_inter]
    constructor
    · rintro (⟨h1, h2, -⟩ | ⟨h1, h2, -⟩) <;> exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      have : u ∈ V₁ ∪ V₂ := hV ▸ mem_univ u
      rcases mem_union.mp this with h | h
      · exact Or.inl ⟨h1, h2, h⟩
      · exact Or.inr ⟨h1, h2, h⟩
  have hd : Disjoint ((T ∩ V₁).erase v) ((T ∩ V₂).erase v) := by
    rw [Finset.disjoint_left]
    intro u hu1 hu2
    simp only [mem_erase, mem_inter] at hu1 hu2
    have : u ∈ V₁ ∩ V₂ := mem_inter.mpr ⟨hu1.2.2, hu2.2.2⟩
    rw [hV₁₂, mem_singleton] at this
    exact hu1.1 this
  rw [← card_union_of_disjoint hd, hu]
  by_cases hvT : v ∈ T
  · rw [if_pos hvT, card_erase_add_one hvT]
  · rw [if_neg hvT, erase_eq_of_notMem hvT, add_zero]

theorem deg_union (G : NicerEars.TJoin.Graph V E) (E₁ E₂ : Finset E) (hE₁₂ : Disjoint E₁ E₂)
    (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)) (u : V) :
    #((F₁.map ι ∪ F₂.map ι).filter (fun p => u ∈ G.double.ends p)) =
      #((F₁.map ι).filter (fun p => u ∈ G.double.ends p)) +
      #((F₂.map ι).filter (fun p => u ∈ G.double.ends p)) := by
  rw [filter_union, card_union_of_disjoint]
  apply disjoint_filter_filter
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  obtain ⟨a, -, rfl⟩ := mem_map.mp hp1
  obtain ⟨b, -, hb⟩ := mem_map.mp hp2
  simp only [ι_apply, Prod.mk.injEq] at hb
  exact Finset.disjoint_left.mp hE₁₂ a.1.2 (hb.1 ▸ b.1.2)

theorem deg_other_zero (G : NicerEars.TJoin.Graph V E) (V₂ : Finset V) (E₂ : Finset E)
    (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂) (F₂ : Finset (E₂ × Fin 2)) (u : V) (hu : u ∉ V₂) :
    #((F₂.map ι).filter (fun p => u ∈ G.double.ends p)) = 0 := by
  rw [card_eq_zero, filter_eq_empty_iff]
  intro p hp hup
  obtain ⟨a, -, rfl⟩ := mem_map.mp hp
  exact hu (h₂ _ a.1.2 u hup)

/-- union of a T₁-join and a T₂-join is a T-join -/
theorem union_tjoin (G : NicerEars.TJoin.Graph V E) (v : V) (V₁ V₂ : Finset V)
    (E₁ E₂ : Finset E) (hV : V₁ ∪ V₂ = univ) (hV₁₂ : V₁ ∩ V₂ = {v}) (hE₁₂ : Disjoint E₁ E₂)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂)
    (T : Finset V) (hT : Even #T) (T₁ : Finset V₁) (T₂ : Finset V₂)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁)))
    (hT₂ : Even #T₂ ∧ (T₂.map (Function.Embedding.subtype _) = (T ∩ V₂).erase v ∨
      T₂.map (Function.Embedding.subtype _) = insert v (T ∩ V₂)))
    (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2))
    (hF₁ : (G.sub V₁ E₁ h₁).double.IsTJoin T₁ F₁) (hF₂ : (G.sub V₂ E₂ h₂).double.IsTJoin T₂ F₂) :
    G.double.IsTJoin T (F₁.map ι ∪ F₂.map ι) := by
  have hv₁ : v ∈ V₁ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).1
  have hv₂ : v ∈ V₂ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).2
  have hV₂₁ : V₂ ∩ V₁ = {v} := by rw [inter_comm]; exact hV₁₂
  intro u
  rw [deg_union G E₁ E₂ hE₁₂]
  by_cases huv : u = v
  · subst huv
    have d1 := hF₁ ⟨u, hv₁⟩
    have d2 := hF₂ ⟨u, hv₂⟩
    rw [deg_sub] at d1 d2
    simp only at d1 d2
    rw [T_side_v V₁ u hv₁ T T₁ hT₁] at d1
    rw [T_side_v V₂ u hv₂ T T₂ hT₂] at d2
    have hc := card_T_split u V₁ V₂ hV hV₁₂ T
    revert d1 d2 hc hT
    generalize #((F₁.map ι).filter (fun p => u ∈ G.double.ends p)) = a
    generalize #((F₂.map ι).filter (fun p => u ∈ G.double.ends p)) = b
    generalize #((T ∩ V₁).erase u) = t₁
    generalize #((T ∩ V₂).erase u) = t₂
    generalize #T = t
    intro hT d1 d2 hc
    by_cases hu : u ∈ T
    · rw [if_pos hu] at hc
      simp only [hu, iff_true]
      simp only [Nat.odd_iff, Nat.even_iff] at *
      omega
    · rw [if_neg hu] at hc
      simp only [hu, iff_false]
      simp only [Nat.odd_iff, Nat.even_iff] at *
      omega
  · have : u ∈ V₁ ∪ V₂ := hV ▸ mem_univ u
    rcases mem_union.mp this with hu | hu
    · have hu2 : u ∉ V₂ := fun h => huv (by
        have : u ∈ V₁ ∩ V₂ := mem_inter.mpr ⟨hu, h⟩
        rwa [hV₁₂, mem_singleton] at this)
      rw [deg_other_zero G V₂ E₂ h₂ F₂ u hu2, add_zero]
      have := hF₁ ⟨u, hu⟩
      rw [deg_sub] at this
      rw [this, T_side_mem V₁ v T T₁ hT₁.2 ⟨u, hu⟩ huv]
    · have hu1 : u ∉ V₁ := fun h => huv (by
        have : u ∈ V₁ ∩ V₂ := mem_inter.mpr ⟨h, hu⟩
        rwa [hV₁₂, mem_singleton] at this)
      rw [deg_other_zero G V₁ E₁ h₁ F₁ u hu1, zero_add]
      have := hF₂ ⟨u, hu⟩
      rw [deg_sub] at this
      rw [this, T_side_mem V₂ v T T₂ hT₂.2 ⟨u, hu⟩ huv]


theorem cut_iff (G : NicerEars.TJoin.Graph V E) (W : Finset V) (e : E) (a b : V)
    (he : G.ends e = s(a, b)) :
    e ∈ G.cut W ↔ (a ∈ W ∧ b ∉ W) ∨ (b ∈ W ∧ a ∉ W) := by
  simp only [NicerEars.TJoin.Graph.cut, mem_filter, mem_univ, true_and, he, Sym2.eq_iff]
  constructor
  · rintro ⟨u, hu, v, hv, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · exact ⟨a, ha, b, hb, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨b, hb, a, ha, Or.inr ⟨rfl, rfl⟩⟩

theorem crossing_iff (G : NicerEars.TJoin.Graph V E) (P : Finpartition (univ : Finset V)) (e : E)
    (a b : V) (he : G.ends e = s(a, b)) : e ∈ G.crossing P ↔ P.part a ≠ P.part b := by
  simp only [NicerEars.TJoin.Graph.crossing, mem_filter, mem_univ, true_and, he]
  constructor
  · rintro ⟨u, w, h, hne⟩
    rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hne
    · exact fun h' => hne h'.symm
  · intro h; exact ⟨a, b, rfl, h⟩

/-- a partition realising the fibres of a function -/
theorem exists_partition_of_fun {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) : ∃ P : Finpartition (univ : Finset α), #P.parts = #(univ.image f) ∧
      ∀ a b, P.part a = P.part b ↔ f a = f b := by
  let fib : β → Finset α := fun y => univ.filter (fun a => f a = y)
  have hinj : Set.InjOn fib ↑(univ.image f) := by
    intro y hy y' _ h
    obtain ⟨a, -, rfl⟩ := mem_image.mp hy
    have : a ∈ fib (f a) := by simp [fib]
    rw [h] at this
    simpa [fib] using this
  let P : Finpartition (univ : Finset α) := Finpartition.ofExistsUnique
    ((univ.image f).image fib) (fun _ _ => subset_univ _)
    (fun a _ => ⟨fib (f a), ⟨mem_image_of_mem _ (mem_image_of_mem _ (mem_univ a)),
      by simp [fib]⟩, by
        rintro t ⟨ht, hat⟩
        obtain ⟨y, -, rfl⟩ := mem_image.mp ht
        simp only [fib, mem_filter, mem_univ, true_and] at hat
        rw [hat]⟩)
    (by
      intro h
      obtain ⟨y, hy, hfy⟩ := mem_image.mp h
      obtain ⟨a, -, rfl⟩ := mem_image.mp hy
      have : a ∈ fib (f a) := by simp [fib]
      rw [hfy] at this
      exact notMem_empty a this)
  have hpart : ∀ a, P.part a = fib (f a) := by
    intro a
    apply P.part_eq_of_mem
    · show fib (f a) ∈ (univ.image f).image fib
      exact mem_image_of_mem _ (mem_image_of_mem _ (mem_univ a))
    · simp [fib]
  refine ⟨P, ?_, ?_⟩
  · show #((univ.image f).image fib) = _
    exact card_image_of_injOn hinj
  · intro a b
    rw [hpart, hpart]
    constructor
    · intro h
      exact hinj (mem_image_of_mem _ (mem_univ a)) (mem_image_of_mem _ (mem_univ b)) h
    · intro h; rw [h]

theorem parts_eq_image (P : Finpartition (univ : Finset V)) : P.parts = univ.image P.part := by
  ext t
  constructor
  · intro ht
    obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts ht
    exact mem_image.mpr ⟨a, mem_univ a, P.part_eq_of_mem ht ha⟩
  · intro ht
    obtain ⟨a, -, rfl⟩ := mem_image.mp ht
    exact P.part_mem.mpr (mem_univ a)

theorem sum_map_sub {F : Finset E} (x : E → ℝ) (S : Finset F) :
    ∑ e ∈ S.map (Function.Embedding.subtype _), x e = ∑ e ∈ S, x e.1 := by
  rw [sum_map]; rfl

/-- `x(δ(A)) ≥ 1` from the partition constraints for a nonempty proper `A`. -/
theorem cut_ge_one {V' E' : Type} [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
    (G : NicerEars.TJoin.Graph V' E') (T : Finset V') (x : E' → ℝ) (hx : G.LPTFeasible T x)
    (A : Finset V') (hA : A.Nonempty) (hAu : A ≠ univ) : 1 ≤ ∑ e ∈ G.cut A, x e := by
  obtain ⟨P, hP, hpart⟩ := exists_partition_of_fun (fun u : V' => decide (u ∈ A))
  have h2 : #(univ.image (fun u : V' => decide (u ∈ A))) = 2 := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨b, hb⟩ : ∃ b, b ∉ A := by
      by_contra h; push_neg at h; exact hAu (eq_univ_of_forall h)
    have : univ.image (fun u : V' => decide (u ∈ A)) = {true, false} := by
      ext t
      simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
      constructor
      · intro _; cases t <;> simp
      · rintro (rfl | rfl)
        · exact ⟨a, by simp [ha]⟩
        · exact ⟨b, by simp [hb]⟩
    rw [this]; rfl
  have hc := hx.2.2 P
  rw [hP, h2] at hc
  have hsub : G.crossing P ⊆ G.cut A := by
    intro e he
    obtain ⟨a, b, -, hab⟩ := ends_rep G e
    rw [crossing_iff G P e a b hab, Ne, hpart] at he
    rw [SolProp4Aux.cut_iff G A e a b hab]
    by_cases ha : a ∈ A <;> by_cases hb : b ∈ A <;> simp_all
  have : ∑ e ∈ G.crossing P, x e ≤ ∑ e ∈ G.cut A, x e :=
    sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx.1 e)
  push_cast at hc
  linarith


theorem card_erase_ind {α : Type} [DecidableEq α] (s : Finset α) (a : α) :
    #s = #(s.erase a) + (if a ∈ s then 1 else 0) := by
  by_cases h : a ∈ s
  · rw [if_pos h, card_erase_add_one h]
  · rw [if_neg h, erase_eq_of_notMem h, add_zero]

theorem map_inter_erase (V₁ : Finset V) (v : V) (T : Finset V) (T₁ : Finset V₁)
    (hT₁ : T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁))
    (A : Finset V₁) (hv₁ : v ∈ V₁) :
    ((A ∩ T₁).erase ⟨v, hv₁⟩).map (Function.Embedding.subtype _) =
      ((A.map (Function.Embedding.subtype _)) ∩ T).erase v := by
  ext u
  simp only [mem_map, mem_erase, mem_inter, Function.Embedding.coe_subtype]
  constructor
  · rintro ⟨a, ⟨hav, haA, haT⟩, rfl⟩
    have hav' : a.1 ≠ v := fun h => hav (Subtype.ext h)
    exact ⟨hav', ⟨a, haA, rfl⟩, (T_side_mem V₁ v T T₁ hT₁ a hav').mp haT⟩
  · rintro ⟨huv, ⟨a, haA, rfl⟩, huT⟩
    exact ⟨a, ⟨fun h => huv (congrArg Subtype.val h), haA,
      (T_side_mem V₁ v T T₁ hT₁ a huv).mpr huT⟩, rfl⟩

theorem parity_lift_notmem (V₁ : Finset V) (v : V) (hv₁ : v ∈ V₁) (T : Finset V) (T₁ : Finset V₁)
    (hT₁ : T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁))
    (A : Finset V₁) (hA : v ∉ A.map (Function.Embedding.subtype _)) :
    #(A ∩ T₁) = #((A.map (Function.Embedding.subtype _)) ∩ T) := by
  have hvA : (⟨v, hv₁⟩ : V₁) ∉ A := fun h => hA (mem_map_of_mem _ h)
  have h1 : (A ∩ T₁).erase ⟨v, hv₁⟩ = A ∩ T₁ :=
    erase_eq_of_notMem (fun h => hvA (mem_inter.mp h).1)
  have h2 : ((A.map (Function.Embedding.subtype _)) ∩ T).erase v =
      (A.map (Function.Embedding.subtype _)) ∩ T :=
    erase_eq_of_notMem (fun h => hA (mem_inter.mp h).1)
  rw [← h1, ← h2, ← map_inter_erase V₁ v T T₁ hT₁ A hv₁, card_map]

theorem parity_lift_mem (v : V) (V₁ V₂ : Finset V) (hV : V₁ ∪ V₂ = univ)
    (hV₁₂ : V₁ ∩ V₂ = {v}) (hv₁ : v ∈ V₁) (T : Finset V) (hT : Even #T) (T₁ : Finset V₁)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁)))
    (A : Finset V₁) (hA : v ∈ A.map (Function.Embedding.subtype _)) :
    Even #(A ∩ T₁) ↔ Even #(((A.map (Function.Embedding.subtype _)) ∪ V₂) ∩ T) := by
  set A' := A.map (Function.Embedding.subtype _)
  have hvA : (⟨v, hv₁⟩ : V₁) ∈ A := by
    obtain ⟨a, ha, hav⟩ := mem_map.mp hA
    have : a = ⟨v, hv₁⟩ := Subtype.ext hav
    rwa [← this]
  have hi : #(A ∩ T₁) = #((A' ∩ T).erase v) + (if (⟨v, hv₁⟩ : V₁) ∈ T₁ then 1 else 0) := by
    rw [card_erase_ind (A ∩ T₁) ⟨v, hv₁⟩, ← card_map, map_inter_erase V₁ v T T₁ hT₁.2 A hv₁]
    simp [hvA, A']
  have hii : #((A' ∪ V₂) ∩ T) = #((A' ∩ T).erase v) + #((T ∩ V₂).erase v) +
      (if v ∈ T then 1 else 0) := by
    have hsplit : ((A' ∪ V₂) ∩ T).erase v = (A' ∩ T).erase v ∪ (T ∩ V₂).erase v := by
      ext u; simp only [mem_erase, mem_inter, mem_union]; tauto
    have hd : Disjoint ((A' ∩ T).erase v) ((T ∩ V₂).erase v) := by
      rw [Finset.disjoint_left]
      intro u hu1 hu2
      simp only [mem_erase, mem_inter] at hu1 hu2
      have hu1' : u ∈ V₁ := by
        obtain ⟨a, -, rfl⟩ := mem_map.mp hu1.2.1
        exact a.2
      have : u ∈ V₁ ∩ V₂ := mem_inter.mpr ⟨hu1', hu2.2.2⟩
      rw [hV₁₂, mem_singleton] at this
      exact hu1.1 this
    rw [card_erase_ind ((A' ∪ V₂) ∩ T) v, hsplit, card_union_of_disjoint hd]
    have : v ∈ (A' ∪ V₂) ∩ T ↔ v ∈ T := by simp [hA]
    simp only [this]
  have hiii := T_side_v V₁ v hv₁ T T₁ hT₁
  have hc := card_T_split v V₁ V₂ hV hV₁₂ T
  rw [hi, hii]
  revert hiii hc hT
  generalize #((A' ∩ T).erase v) = c
  generalize #((T ∩ V₁).erase v) = t₁
  generalize #((T ∩ V₂).erase v) = t₂
  generalize #T = t
  intro hT hiii hc
  by_cases h1 : (⟨v, hv₁⟩ : V₁) ∈ T₁ <;> by_cases h2 : v ∈ T <;>
    simp only [h1, h2, if_true, if_false, true_iff, false_iff] at hiii hc ⊢ <;>
    simp only [Nat.odd_iff, Nat.even_iff] at * <;> omega


theorem mem_lift {W : Finset V} (A : Finset W) (a : W) :
    a.1 ∈ A.map (Function.Embedding.subtype _) ↔ a ∈ A :=
  Finset.mem_map' (Function.Embedding.subtype _)

theorem lift_sub {W : Finset V} (A : Finset W) : A.map (Function.Embedding.subtype _) ⊆ W := by
  intro u hu
  obtain ⟨a, -, rfl⟩ := mem_map.mp hu
  exact a.2

/-- Part (5): an LP(G,T) solution restricts to an LP(G₁,T₁) solution. -/
theorem lp_restrict (G : NicerEars.TJoin.Graph V E) (v : V) (V₁ V₂ : Finset V)
    (E₁ E₂ : Finset E) (hV : V₁ ∪ V₂ = univ) (hV₁₂ : V₁ ∩ V₂ = {v}) (hE : E₁ ∪ E₂ = univ)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂)
    (T : Finset V) (hT : Even #T) (T₁ : Finset V₁)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁)))
    (x : E → ℝ) (hx : G.LPTFeasible T x) :
    (G.sub V₁ E₁ h₁).LPTFeasible T₁ (fun e => x e.1) := by
  have hv₁ : v ∈ V₁ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).1
  have hv₂ : v ∈ V₂ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).2
  have hboth : ∀ u, u ∈ V₁ → u ∈ V₂ → u = v := by
    intro u h1 h2
    have : u ∈ V₁ ∩ V₂ := mem_inter.mpr ⟨h1, h2⟩
    rwa [hV₁₂, mem_singleton] at this
  -- E₂ edges have all ends in V₂
  have hside : ∀ e, e ∉ E₁ → e ∈ E₂ := by
    intro e he
    have : e ∈ E₁ ∪ E₂ := hE ▸ mem_univ _
    exact (mem_union.mp this).resolve_left he
  refine ⟨fun e => hx.1 e.1, ?_, ?_⟩
  · intro A hA hAu hAT
    set A' := A.map (Function.Embedding.subtype _)
    let W : Finset V := if v ∈ A' then A' ∪ V₂ else A'
    have hWmem : ∀ c ∈ V₁, c ∈ W ↔ c ∈ A' := by
      intro c hc
      by_cases hvA : v ∈ A'
      · simp only [W, if_pos hvA, mem_union]
        constructor
        · rintro (h | h)
          · exact h
          · rw [hboth c hc h]; exact hvA
        · exact Or.inl
      · simp only [W, if_neg hvA]
    have hWne : W.Nonempty := by
      obtain ⟨a, ha⟩ := hA
      exact ⟨a.1, (hWmem a.1 a.2).mpr ((mem_lift A a).mpr ha)⟩
    have hWu : W ≠ univ := by
      obtain ⟨a, ha⟩ : ∃ a, a ∉ A := by
        by_contra h; push_neg at h; exact hAu (eq_univ_of_forall h)
      intro hW
      have : a.1 ∈ W := hW ▸ mem_univ _
      rw [hWmem a.1 a.2, mem_lift] at this
      exact ha this
    have hWT : Even #(W ∩ T) := by
      by_cases hvA : v ∈ A'
      · simp only [W, if_pos hvA]
        exact (parity_lift_mem v V₁ V₂ hV hV₁₂ hv₁ T hT T₁ hT₁ A hvA).mp hAT
      · simp only [W, if_neg hvA]
        rw [← parity_lift_notmem V₁ v hv₁ T T₁ hT₁.2 A hvA]
        exact hAT
    have hc := hx.2.1 W hWne hWu hWT
    have hsub : G.cut W ⊆ ((G.sub V₁ E₁ h₁).cut A).map (Function.Embedding.subtype _) := by
      intro e he
      obtain ⟨a, b, hab, heab⟩ := ends_rep G e
      rw [cut_iff G W e a b heab] at he
      by_cases heE : e ∈ E₁
      · have ha : a ∈ V₁ := h₁ e heE a (by rw [heab]; exact Sym2.mem_mk_left a b)
        have hb : b ∈ V₁ := h₁ e heE b (by rw [heab]; exact Sym2.mem_mk_right a b)
        refine mem_map.mpr ⟨⟨e, heE⟩, ?_, rfl⟩
        rw [cut_iff (G.sub V₁ E₁ h₁) A ⟨e, heE⟩ ⟨a, ha⟩ ⟨b, hb⟩
          ((sub_ends_iff G V₁ E₁ h₁ ⟨e, heE⟩ ⟨a, ha⟩ ⟨b, hb⟩).mpr heab)]
        rw [hWmem a ha, hWmem b hb] at he
        rw [← mem_lift A ⟨a, ha⟩, ← mem_lift A ⟨b, hb⟩]
        exact he
      · exfalso
        have he2 := hside e heE
        have ha : a ∈ V₂ := h₂ e he2 a (by rw [heab]; exact Sym2.mem_mk_left a b)
        have hb : b ∈ V₂ := h₂ e he2 b (by rw [heab]; exact Sym2.mem_mk_right a b)
        have key : ∀ c ∈ V₂, c ∈ W ↔ v ∈ A' := by
          intro c hc
          by_cases hvA : v ∈ A'
          · simp only [W, if_pos hvA, mem_union, hc, or_true, hvA]
          · simp only [W, if_neg hvA, hvA, iff_false]
            intro hcA
            have := hboth c (lift_sub A hcA) hc
            exact hvA (this ▸ hcA)
        rw [key a ha, key b hb] at he
        tauto
    have : ∑ e ∈ G.cut W, x e ≤ ∑ e ∈ ((G.sub V₁ E₁ h₁).cut A).map
        (Function.Embedding.subtype _), x e :=
      sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx.1 e)
    rw [sum_map_sub] at this
    linarith
  · intro P₁
    let π : V → V₁ := fun u => if h : u ∈ V₁ then ⟨u, h⟩ else ⟨v, hv₁⟩
    have hπ : ∀ a : V₁, π a.1 = a := by
      intro a; simp [π, a.2]
    have hπ2 : ∀ u ∈ V₂, π u = ⟨v, hv₁⟩ := by
      intro u hu
      by_cases h : u ∈ V₁
      · have := hboth u h hu
        subst this; simp [π, hv₁]
      · simp [π, h]
    obtain ⟨P, hPc, hPp⟩ := exists_partition_of_fun (fun u => P₁.part (π u))
    have himg : univ.image (fun u => P₁.part (π u)) = P₁.parts := by
      rw [parts_eq_image P₁]
      ext t
      simp only [mem_image, mem_univ, true_and]
      constructor
      · rintro ⟨u, rfl⟩; exact ⟨π u, rfl⟩
      · rintro ⟨a, rfl⟩; exact ⟨a.1, by rw [hπ]⟩
    have hc := hx.2.2 P
    rw [hPc, himg] at hc
    have hsub : G.crossing P ⊆
        ((G.sub V₁ E₁ h₁).crossing P₁).map (Function.Embedding.subtype _) := by
      intro e he
      obtain ⟨a, b, hab, heab⟩ := ends_rep G e
      rw [crossing_iff G P e a b heab, Ne, hPp] at he
      by_cases heE : e ∈ E₁
      · have ha : a ∈ V₁ := h₁ e heE a (by rw [heab]; exact Sym2.mem_mk_left a b)
        have hb : b ∈ V₁ := h₁ e heE b (by rw [heab]; exact Sym2.mem_mk_right a b)
        refine mem_map.mpr ⟨⟨e, heE⟩, ?_, rfl⟩
        rw [crossing_iff (G.sub V₁ E₁ h₁) P₁ ⟨e, heE⟩ ⟨a, ha⟩ ⟨b, hb⟩
          ((sub_ends_iff G V₁ E₁ h₁ ⟨e, heE⟩ ⟨a, ha⟩ ⟨b, hb⟩).mpr heab)]
        have h1 : π a = ⟨a, ha⟩ := hπ ⟨a, ha⟩
        have h2 : π b = ⟨b, hb⟩ := hπ ⟨b, hb⟩
        rw [h1, h2] at he
        exact he
      · exfalso
        have he2 := hside e heE
        have ha : a ∈ V₂ := h₂ e he2 a (by rw [heab]; exact Sym2.mem_mk_left a b)
        have hb : b ∈ V₂ := h₂ e he2 b (by rw [heab]; exact Sym2.mem_mk_right a b)
        rw [hπ2 a ha, hπ2 b hb] at he
        exact he rfl
    have : ∑ e ∈ G.crossing P, x e ≤ ∑ e ∈ ((G.sub V₁ E₁ h₁).crossing P₁).map
        (Function.Embedding.subtype _), x e :=
      sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ => hx.1 e)
    rw [sum_map_sub] at this
    linarith


theorem side_even (v : V) (V₁ V₂ : Finset V) (hV : V₁ ∪ V₂ = univ) (hV₁₂ : V₁ ∩ V₂ = {v})
    (T : Finset V) (hT : Even #T) (T₁ : Finset V₁)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁)))
    (W : Finset V) (hB : (∀ u ∈ V₂, u ∉ W) ∨ V₂ ⊆ W) (hW : Even #(W ∩ T)) :
    Even #((univ.filter (fun a : V₁ => a.1 ∈ W)) ∩ T₁) := by
  have hv₁ : v ∈ V₁ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).1
  have hv₂ : v ∈ V₂ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).2
  set A := univ.filter (fun a : V₁ => a.1 ∈ W)
  have hA' : ∀ u, u ∈ A.map (Function.Embedding.subtype _) ↔ u ∈ W ∧ u ∈ V₁ := by
    intro u
    simp only [mem_map, A, mem_filter, mem_univ, true_and, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨ha, a.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨u, h2⟩, h1, rfl⟩
  rcases hB with hB | hB
  · have hvA : v ∉ A.map (Function.Embedding.subtype _) := fun h =>
      hB v hv₂ ((hA' v).mp h).1
    have heq : A.map (Function.Embedding.subtype _) = W := by
      ext u
      rw [hA']
      constructor
      · exact fun h => h.1
      · intro hu
        refine ⟨hu, ?_⟩
        have : u ∈ V₁ ∪ V₂ := hV ▸ mem_univ u
        rcases mem_union.mp this with h | h
        · exact h
        · exact absurd hu (hB u h)
    rw [parity_lift_notmem V₁ v hv₁ T T₁ hT₁.2 A hvA, heq]
    exact hW
  · have hvA : v ∈ A.map (Function.Embedding.subtype _) := (hA' v).mpr ⟨hB hv₂, hv₁⟩
    have heq : A.map (Function.Embedding.subtype _) ∪ V₂ = W := by
      ext u
      rw [mem_union, hA']
      constructor
      · rintro (h | h)
        · exact h.1
        · exact hB h
      · intro hu
        have : u ∈ V₁ ∪ V₂ := hV ▸ mem_univ u
        rcases mem_union.mp this with h | h
        · exact Or.inl ⟨hu, h⟩
        · exact Or.inr h
    rw [parity_lift_mem v V₁ V₂ hV hV₁₂ hv₁ T hT T₁ hT₁ A hvA, heq]
    exact hW

theorem sum_two_le (E₁ E₂ : Finset E) (hE₁₂ : Disjoint E₁ E₂) (x : E → ℝ) (hx0 : ∀ e, 0 ≤ x e)
    (S : Finset E) (S₁ : Finset E₁) (S₂ : Finset E₂)
    (h1 : S₁.map (Function.Embedding.subtype _) ⊆ S)
    (h2 : S₂.map (Function.Embedding.subtype _) ⊆ S) :
    ∑ e ∈ S₁, x e.1 + ∑ e ∈ S₂, x e.1 ≤ ∑ e ∈ S, x e := by
  rw [← sum_map_sub, ← sum_map_sub, ← sum_union]
  · exact sum_le_sum_of_subset_of_nonneg (union_subset h1 h2) (fun e _ _ => hx0 e)
  · exact Finset.disjoint_of_subset_left (lift_sub _)
      (Finset.disjoint_of_subset_right (lift_sub _) hE₁₂)

theorem cut_lift (G : NicerEars.TJoin.Graph V E) (W : Finset V) (V₁ : Finset V) (E₁ : Finset E)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) :
    ((G.sub V₁ E₁ h₁).cut (univ.filter (fun a : V₁ => a.1 ∈ W))).map
      (Function.Embedding.subtype _) ⊆ G.cut W := by
  intro e he
  obtain ⟨e₁, he₁, rfl⟩ := mem_map.mp he
  obtain ⟨a, b, hab, heab⟩ := ends_rep (G.sub V₁ E₁ h₁) e₁
  rw [cut_iff _ _ e₁ a b heab] at he₁
  show e₁.1 ∈ G.cut W
  rw [cut_iff G W e₁.1 a.1 b.1 ((sub_ends_iff G V₁ E₁ h₁ e₁ a b).mp heab)]
  simpa using he₁

theorem crossing_lift (G : NicerEars.TJoin.Graph V E) (P : Finpartition (univ : Finset V))
    (V₁ : Finset V) (E₁ : Finset E) (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁)
    (P₁ : Finpartition (univ : Finset V₁))
    (hP₁ : ∀ a b, P₁.part a = P₁.part b ↔ P.part a.1 = P.part b.1) :
    ((G.sub V₁ E₁ h₁).crossing P₁).map (Function.Embedding.subtype _) ⊆ G.crossing P := by
  intro e he
  obtain ⟨e₁, he₁, rfl⟩ := mem_map.mp he
  obtain ⟨a, b, hab, heab⟩ := ends_rep (G.sub V₁ E₁ h₁) e₁
  rw [crossing_iff _ _ e₁ a b heab, Ne, hP₁] at he₁
  show e₁.1 ∈ G.crossing P
  rw [crossing_iff G P e₁.1 a.1 b.1 ((sub_ends_iff G V₁ E₁ h₁ e₁ a b).mp heab)]
  exact he₁


/-- Part (6): LP(G₁,T₁) and LP(G₂,T₂) solutions combine into an LP(G,T) solution. -/
theorem lp_combine (G : NicerEars.TJoin.Graph V E) (v : V) (V₁ V₂ : Finset V)
    (E₁ E₂ : Finset E) (hV : V₁ ∪ V₂ = univ) (hV₁₂ : V₁ ∩ V₂ = {v}) (hE : E₁ ∪ E₂ = univ)
    (hE₁₂ : Disjoint E₁ E₂)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂)
    (T : Finset V) (hT : Even #T) (T₁ : Finset V₁) (T₂ : Finset V₂)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁)))
    (hT₂ : Even #T₂ ∧ (T₂.map (Function.Embedding.subtype _) = (T ∩ V₂).erase v ∨
      T₂.map (Function.Embedding.subtype _) = insert v (T ∩ V₂)))
    (x₁ : E₁ → ℝ) (x₂ : E₂ → ℝ) (hx₁ : (G.sub V₁ E₁ h₁).LPTFeasible T₁ x₁)
    (hx₂ : (G.sub V₂ E₂ h₂).LPTFeasible T₂ x₂) :
    ∃ x : E → ℝ, G.LPTFeasible T x ∧ ∑ e, x e ≤ ∑ e, x₁ e + ∑ e, x₂ e := by
  have hv₁ : v ∈ V₁ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).1
  have hv₂ : v ∈ V₂ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).2
  have hV' : V₂ ∪ V₁ = univ := by rw [union_comm]; exact hV
  have hV₂₁ : V₂ ∩ V₁ = {v} := by rw [inter_comm]; exact hV₁₂
  let x : E → ℝ := fun e =>
    if h : e ∈ E₁ then x₁ ⟨e, h⟩ else if h' : e ∈ E₂ then x₂ ⟨e, h'⟩ else 0
  have hx1 : ∀ e : E₁, x e.1 = x₁ e := by
    intro e; simp [x, e.2]
  have hx2 : ∀ e : E₂, x e.1 = x₂ e := by
    intro e
    have : e.1 ∉ E₁ := fun h => Finset.disjoint_left.mp hE₁₂ h e.2
    simp [x, this, e.2]
  have hx0 : ∀ e, 0 ≤ x e := by
    intro e
    simp only [x]
    split_ifs with h h'
    · exact hx₁.1 _
    · exact hx₂.1 _
    · exact le_rfl
  have hsum : ∑ e, x e = ∑ e, x₁ e + ∑ e, x₂ e := by
    rw [← hE, sum_union hE₁₂, ← sum_coe_sort E₁, ← sum_coe_sort E₂]
    simp only [hx1, hx2]
  refine ⟨x, ⟨hx0, ?_, ?_⟩, hsum.le⟩
  · intro W hW hWu hWT
    set A := univ.filter (fun a : V₁ => a.1 ∈ W)
    set B := univ.filter (fun a : V₂ => a.1 ∈ W)
    have hsplit := sum_two_le E₁ E₂ hE₁₂ x hx0 (G.cut W) _ _ (cut_lift G W V₁ E₁ h₁)
      (cut_lift G W V₂ E₂ h₂)
    simp only [hx1, hx2] at hsplit
    have hnn1 : 0 ≤ ∑ e ∈ (G.sub V₁ E₁ h₁).cut A, x₁ e := sum_nonneg (fun e _ => hx₁.1 e)
    have hnn2 : 0 ≤ ∑ e ∈ (G.sub V₂ E₂ h₂).cut B, x₂ e := sum_nonneg (fun e _ => hx₂.1 e)
    have hAv : (⟨v, hv₁⟩ : V₁) ∈ A ↔ v ∈ W := by simp [A]
    have hBv : (⟨v, hv₂⟩ : V₂) ∈ B ↔ v ∈ W := by simp [B]
    have hBe : B = ∅ → ∀ u ∈ V₂, u ∉ W := by
      intro h u hu huW
      have : (⟨u, hu⟩ : V₂) ∈ B := by simp [B, huW]
      rw [h] at this; exact notMem_empty _ this
    have hBu : B = univ → V₂ ⊆ W := by
      intro h u hu
      have : (⟨u, hu⟩ : V₂) ∈ B := h ▸ mem_univ _
      simpa [B] using this
    have hAe : A = ∅ → ∀ u ∈ V₁, u ∉ W := by
      intro h u hu huW
      have : (⟨u, hu⟩ : V₁) ∈ A := by simp [A, huW]
      rw [h] at this; exact notMem_empty _ this
    have hAu : A = univ → V₁ ⊆ W := by
      intro h u hu
      have : (⟨u, hu⟩ : V₁) ∈ A := h ▸ mem_univ _
      simpa [A] using this
    have triv : ∀ {α : Type} [Fintype α] (S : Finset α), ¬ (S.Nonempty ∧ S ≠ univ) →
        S = ∅ ∨ S = univ := by
      intro α _ S h
      by_cases h1 : S.Nonempty
      · right; by_contra h2; exact h (⟨h1, h2⟩)
      · left; exact not_nonempty_iff_eq_empty.mp h1
    by_cases pA : A.Nonempty ∧ A ≠ univ <;> by_cases pB : B.Nonempty ∧ B ≠ univ
    · have := cut_ge_one _ T₁ x₁ hx₁ A pA.1 pA.2
      have := cut_ge_one _ T₂ x₂ hx₂ B pB.1 pB.2
      linarith
    · have hB' : (∀ u ∈ V₂, u ∉ W) ∨ V₂ ⊆ W := by
        rcases triv B pB with h | h
        · exact Or.inl (hBe h)
        · exact Or.inr (hBu h)
      have he := side_even v V₁ V₂ hV hV₁₂ T hT T₁ hT₁ W hB' hWT
      have := hx₁.2.1 A pA.1 pA.2 he
      linarith
    · have hA' : (∀ u ∈ V₁, u ∉ W) ∨ V₁ ⊆ W := by
        rcases triv A pA with h | h
        · exact Or.inl (hAe h)
        · exact Or.inr (hAu h)
      have he := side_even v V₂ V₁ hV' hV₂₁ T hT T₂ hT₂ W hA' hWT
      have := hx₂.2.1 B pB.1 pB.2 he
      linarith
    · exfalso
      rcases triv A pA with hA | hA <;> rcases triv B pB with hB | hB
      · obtain ⟨u, hu⟩ := hW
        have : u ∈ V₁ ∪ V₂ := hV ▸ mem_univ u
        rcases mem_union.mp this with h | h
        · exact hAe hA u h hu
        · exact hBe hB u h hu
      · exact hAe hA v hv₁ (hBu hB hv₂)
      · exact hBe hB v hv₂ (hAu hA hv₁)
      · apply hWu
        apply eq_univ_of_forall
        intro u
        have : u ∈ V₁ ∪ V₂ := hV ▸ mem_univ u
        rcases mem_union.mp this with h | h
        · exact hAu hA h
        · exact hBu hB h
  · intro P
    obtain ⟨P₁, hP₁c, hP₁p⟩ := exists_partition_of_fun (fun a : V₁ => P.part a.1)
    obtain ⟨P₂, hP₂c, hP₂p⟩ := exists_partition_of_fun (fun a : V₂ => P.part a.1)
    have c1 := hx₁.2.2 P₁
    have c2 := hx₂.2.2 P₂
    rw [hP₁c] at c1
    rw [hP₂c] at c2
    have hsplit := sum_two_le E₁ E₂ hE₁₂ x hx0 (G.crossing P) _ _
      (crossing_lift G P V₁ E₁ h₁ P₁ hP₁p) (crossing_lift G P V₂ E₂ h₂ P₂ hP₂p)
    simp only [hx1, hx2] at hsplit
    set I₁ := univ.image (fun a : V₁ => P.part a.1)
    set I₂ := univ.image (fun a : V₂ => P.part a.1)
    have hunion : P.parts = I₁ ∪ I₂ := by
      rw [parts_eq_image P]
      ext t
      simp only [mem_image, mem_univ, true_and, mem_union, I₁, I₂]
      constructor
      · rintro ⟨u, rfl⟩
        have : u ∈ V₁ ∪ V₂ := hV ▸ mem_univ u
        rcases mem_union.mp this with h | h
        · exact Or.inl ⟨⟨u, h⟩, rfl⟩
        · exact Or.inr ⟨⟨u, h⟩, rfl⟩
      · rintro (⟨a, rfl⟩ | ⟨a, rfl⟩) <;> exact ⟨a.1, rfl⟩
    have hinter : 1 ≤ #(I₁ ∩ I₂) := by
      apply card_pos.mpr
      refine ⟨P.part v, mem_inter.mpr ⟨?_, ?_⟩⟩
      · exact mem_image.mpr ⟨⟨v, hv₁⟩, mem_univ _, rfl⟩
      · exact mem_image.mpr ⟨⟨v, hv₂⟩, mem_univ _, rfl⟩
    have hcard := card_union_add_card_inter I₁ I₂
    rw [← hunion] at hcard
    have : (#P.parts : ℝ) + 1 ≤ #I₁ + #I₂ := by
      have : #P.parts + 1 ≤ #I₁ + #I₂ := by omega
      exact_mod_cast this
    linarith

end SolProp4Aux

open SolProp4Aux in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TJoin.Graph V E) (v : V) (V₁ V₂ : Finset V) (E₁ E₂ : Finset E)
    (hV : V₁ ∪ V₂ = univ) (hV₁₂ : V₁ ∩ V₂ = {v}) (hE : E₁ ∪ E₂ = univ) (hE₁₂ : Disjoint E₁ E₂)
    (h₁ : ∀ e ∈ E₁, ∀ u ∈ G.ends e, u ∈ V₁) (h₂ : ∀ e ∈ E₂, ∀ u ∈ G.ends e, u ∈ V₂)
    (hG₁ : (G.sub V₁ E₁ h₁).IsConnected) (hG₂ : (G.sub V₂ E₂ h₂).IsConnected)
    (T : Finset V) (hT : Even #T) (T₁ : Finset V₁) (T₂ : Finset V₂)
    (hT₁ : Even #T₁ ∧ (T₁.map (Function.Embedding.subtype _) = (T ∩ V₁).erase v ∨
      T₁.map (Function.Embedding.subtype _) = insert v (T ∩ V₁)))
    (hT₂ : Even #T₂ ∧ (T₂.map (Function.Embedding.subtype _) = (T ∩ V₂).erase v ∨
      T₂.map (Function.Embedding.subtype _) = insert v (T ∩ V₂))) :
    -- OPT(G, T) ≥ OPT(G₁, T₁) + OPT(G₂, T₂)
    (∀ F : Finset (E × Fin 2), G.IsConnectedTJoin T F →
      ∃ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
        (G.sub V₁ E₁ h₁).IsConnectedTJoin T₁ F₁ ∧ (G.sub V₂ E₂ h₂).IsConnectedTJoin T₂ F₂ ∧
        #F₁ + #F₂ ≤ #F) ∧
    -- OPT(G, T) ≤ OPT(G₁, T₁) + OPT(G₂, T₂)
    (∀ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
      (G.sub V₁ E₁ h₁).IsConnectedTJoin T₁ F₁ → (G.sub V₂ E₂ h₂).IsConnectedTJoin T₂ F₂ →
      ∃ F : Finset (E × Fin 2), G.IsConnectedTJoin T F ∧ #F ≤ #F₁ + #F₂) ∧
    -- OPT_2EC(G) ≥ OPT_2EC(G₁) + OPT_2EC(G₂)
    (∀ F : Finset (E × Fin 2), G.double.IsTwoECSpanning F →
      ∃ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
        (G.sub V₁ E₁ h₁).double.IsTwoECSpanning F₁ ∧ (G.sub V₂ E₂ h₂).double.IsTwoECSpanning F₂ ∧
        #F₁ + #F₂ ≤ #F) ∧
    -- OPT_2EC(G) ≤ OPT_2EC(G₁) + OPT_2EC(G₂)
    (∀ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
      (G.sub V₁ E₁ h₁).double.IsTwoECSpanning F₁ → (G.sub V₂ E₂ h₂).double.IsTwoECSpanning F₂ →
      ∃ F : Finset (E × Fin 2), G.double.IsTwoECSpanning F ∧ #F ≤ #F₁ + #F₂) ∧
    -- LP(G, T) ≥ LP(G₁, T₁) + LP(G₂, T₂)
    (∀ x : E → ℝ, G.LPTFeasible T x →
      ∃ (x₁ : E₁ → ℝ) (x₂ : E₂ → ℝ), (G.sub V₁ E₁ h₁).LPTFeasible T₁ x₁ ∧
        (G.sub V₂ E₂ h₂).LPTFeasible T₂ x₂ ∧ ∑ e, x₁ e + ∑ e, x₂ e ≤ ∑ e, x e) ∧
    -- LP(G, T) ≤ LP(G₁, T₁) + LP(G₂, T₂)
    (∀ (x₁ : E₁ → ℝ) (x₂ : E₂ → ℝ), (G.sub V₁ E₁ h₁).LPTFeasible T₁ x₁ →
      (G.sub V₂ E₂ h₂).LPTFeasible T₂ x₂ →
      ∃ x : E → ℝ, G.LPTFeasible T x ∧ ∑ e, x e ≤ ∑ e, x₁ e + ∑ e, x₂ e) := by
  have hv₁ : v ∈ V₁ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).1
  have hv₂ : v ∈ V₂ := (mem_inter.mp (hV₁₂ ▸ mem_singleton_self v : v ∈ V₁ ∩ V₂)).2
  have hV₂₁ : V₂ ∩ V₁ = {v} := by rw [inter_comm]; exact hV₁₂
  have hE' : E₂ ∪ E₁ = univ := by rw [union_comm]; exact hE
  -- cardinality of the two restrictions
  have hcardR : ∀ F : Finset (E × Fin 2), #(R E₁ F) + #(R E₂ F) ≤ #F := by
    intro F
    rw [← card_map ι, ← card_map ι (s := R E₂ F), map_R, map_R]
    have hsub : F.filter (fun p => p.1 ∈ E₂) ⊆ F.filter (fun p => ¬ p.1 ∈ E₁) := by
      intro p hp
      simp only [mem_filter] at hp ⊢
      exact ⟨hp.1, fun h => Finset.disjoint_left.mp hE₁₂ h hp.2⟩
    have := card_filter_add_card_filter_not (s := F) (fun p => p.1 ∈ E₁)
    have := card_le_card hsub
    omega
  have hcardU : ∀ (F₁ : Finset (E₁ × Fin 2)) (F₂ : Finset (E₂ × Fin 2)),
      #(F₁.map ι ∪ F₂.map ι) ≤ #F₁ + #F₂ := by
    intro F₁ F₂
    calc #(F₁.map ι ∪ F₂.map ι) ≤ #(F₁.map ι) + #(F₂.map ι) := card_union_le _ _
      _ = #F₁ + #F₂ := by rw [card_map, card_map]
  have hsumx : ∀ x : E → ℝ, ∑ e : E₁, x e.1 + ∑ e : E₂, x e.1 = ∑ e, x e := by
    intro x
    rw [sum_coe_sort E₁ x, sum_coe_sort E₂ x, ← sum_union hE₁₂, hE]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro F hF
    refine ⟨R E₁ F, R E₂ F, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hcardR F⟩
    · exact restrict_tjoin G v V₁ V₂ E₁ E₂ hV₁₂ hE h₁ h₂ T T₁ hT₁ F hF.1
    · exact restrict_connected G v V₁ V₂ E₁ E₂ hV₁₂ hE hv₁ h₁ h₂ F hF.2
    · exact restrict_tjoin G v V₂ V₁ E₂ E₁ hV₂₁ hE' h₂ h₁ T T₂ hT₂ F hF.1
    · exact restrict_connected G v V₂ V₁ E₂ E₁ hV₂₁ hE' hv₂ h₂ h₁ F hF.2
  · intro F₁ F₂ hF₁ hF₂
    refine ⟨F₁.map ι ∪ F₂.map ι, ⟨?_, ?_⟩, hcardU F₁ F₂⟩
    · exact union_tjoin G v V₁ V₂ E₁ E₂ hV hV₁₂ hE₁₂ h₁ h₂ T hT T₁ T₂ hT₁ hT₂ F₁ F₂ hF₁.1 hF₂.1
    · exact union_connected G v V₁ V₂ E₁ E₂ hV hv₁ hv₂ h₁ h₂ F₁ F₂ hF₁.2 hF₂.2
  · intro F hF
    refine ⟨R E₁ F, R E₂ F, ⟨?_, ?_⟩, ⟨?_, ?_⟩, hcardR F⟩
    · exact restrict_connected G v V₁ V₂ E₁ E₂ hV₁₂ hE hv₁ h₁ h₂ F hF.1
    · intro p hp
      rw [← R_erase]
      have : ι p ∈ F := (mem_filter.mp hp).2
      exact restrict_connected G v V₁ V₂ E₁ E₂ hV₁₂ hE hv₁ h₁ h₂ _ (hF.2 _ this)
    · exact restrict_connected G v V₂ V₁ E₂ E₁ hV₂₁ hE' hv₂ h₂ h₁ F hF.1
    · intro p hp
      rw [← R_erase]
      have : ι p ∈ F := (mem_filter.mp hp).2
      exact restrict_connected G v V₂ V₁ E₂ E₁ hV₂₁ hE' hv₂ h₂ h₁ _ (hF.2 _ this)
  · intro F₁ F₂ hF₁ hF₂
    refine ⟨F₁.map ι ∪ F₂.map ι, ⟨?_, ?_⟩, hcardU F₁ F₂⟩
    · exact union_connected G v V₁ V₂ E₁ E₂ hV hv₁ hv₂ h₁ h₂ F₁ F₂ hF₁.1 hF₂.1
    · intro p hp
      have hdisj : Disjoint (F₁.map ι) (F₂.map ι) := by
        rw [Finset.disjoint_left]
        intro q hq1 hq2
        obtain ⟨a, -, rfl⟩ := mem_map.mp hq1
        obtain ⟨b, -, hb⟩ := mem_map.mp hq2
        simp only [ι_apply, Prod.mk.injEq] at hb
        exact Finset.disjoint_left.mp hE₁₂ a.1.2 (hb.1 ▸ b.1.2)
      rcases mem_union.mp hp with hp1 | hp2
      · obtain ⟨p₁, hp₁, rfl⟩ := mem_map.mp hp1
        have hnot : ι p₁ ∉ F₂.map ι := fun h => Finset.disjoint_left.mp hdisj hp1 h
        rw [erase_union_distrib, erase_eq_of_notMem hnot, ← map_erase]
        exact union_connected G v V₁ V₂ E₁ E₂ hV hv₁ hv₂ h₁ h₂ _ F₂ (hF₁.2 p₁ hp₁) hF₂.1
      · obtain ⟨p₂, hp₂, rfl⟩ := mem_map.mp hp2
        have hnot : ι p₂ ∉ F₁.map ι := fun h => Finset.disjoint_left.mp hdisj h hp2
        rw [erase_union_distrib, erase_eq_of_notMem hnot, ← map_erase]
        exact union_connected G v V₁ V₂ E₁ E₂ hV hv₁ hv₂ h₁ h₂ F₁ _ hF₁.1 (hF₂.2 p₂ hp₂)
  · intro x hx
    refine ⟨fun e => x e.1, fun e => x e.1, ?_, ?_, (hsumx x).le⟩
    · exact lp_restrict G v V₁ V₂ E₁ E₂ hV hV₁₂ hE h₁ h₂ T hT T₁ hT₁ x hx
    · have hV' : V₂ ∪ V₁ = univ := by rw [union_comm]; exact hV
      exact lp_restrict G v V₂ V₁ E₂ E₁ hV' hV₂₁ hE' h₂ h₁ T hT T₂ hT₂ x hx
  · intro x₁ x₂ hx₁ hx₂
    exact lp_combine G v V₁ V₂ E₁ E₂ hV hV₁₂ hE hE₁₂ h₁ h₂ T hT T₁ T₂ hT₁ hT₂ x₁ x₂ hx₁ hx₂
