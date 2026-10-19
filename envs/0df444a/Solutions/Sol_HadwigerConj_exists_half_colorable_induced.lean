-- Prove2me | solution 1 for HadwigerConj.exists_half_colorable_induced
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:55:28.459712+00:00
-- url     : https://prove2.me/submissions/caab9c3c-b4a1-45b0-990a-cf5069579b84

import Mathlib
import Definitions.Def_HadwigerConj_Defs

namespace DiracK4
open HadwigerConj SimpleGraph

lemma walk_prop {W : Type*} {G' : SimpleGraph W} {s : Set W} (P : W → Prop)
    (hc : (G'.induce s).Preconnected) {y1 : W} (h1 : y1 ∈ s) (hP1 : P y1)
    (hstep : ∀ y z, y ∈ s → z ∈ s → G'.Adj y z → P y → P z) : ∀ y ∈ s, P y := by
  intro y hy
  obtain ⟨p⟩ := hc ⟨y1, h1⟩ ⟨y, hy⟩
  suffices ∀ (a b : s) (_ : (G'.induce s).Walk a b), P a → P b from this _ _ p hP1
  intro a b q
  induction q with
  | nil => exact id
  | cons h _ ih => exact fun ha => ih (hstep _ _ (Subtype.prop _) (Subtype.prop _) (by simpa using h) ha)

lemma reach_in {V : Type*} {G : SimpleGraph V} {s t : Set V} (hst : s ⊆ t)
    (hs : (G.induce s).Connected) {a b : V} (ha : a ∈ s) (hb : b ∈ s) :
    (G.induce t).Reachable ⟨a, hst ha⟩ ⟨b, hst hb⟩ :=
  (hs.preconnected ⟨a, ha⟩ ⟨b, hb⟩).map (G.induceHomOfLE hst).toHom

lemma minor_trans {U W V : Type*} {H : SimpleGraph U} {G' : SimpleGraph W} {G : SimpleGraph V}
    (h1 : IsMinor H G') (h2 : IsMinor G' G) : IsMinor H G := by
  obtain ⟨B, hBc, hBd, hBa⟩ := h1
  obtain ⟨C, hCc, hCd, hCa⟩ := h2
  refine ⟨fun w => ⋃ y ∈ B w, C y, fun w => ?_, fun w1 w2 hw => ?_, fun w1 w2 hw => ?_⟩
  · set U := ⋃ y ∈ B w, C y with hU
    have hsub : ∀ y ∈ B w, C y ⊆ U := fun y hy => Set.subset_biUnion_of_mem (u := C) hy
    rw [connected_iff]
    obtain ⟨⟨y0, hy0⟩⟩ := (hBc w).nonempty
    obtain ⟨⟨c0, hc0⟩⟩ := (hCc y0).nonempty
    refine ⟨?_, ⟨⟨c0, hsub y0 hy0 hc0⟩⟩⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨y1, hy1, ha'⟩ := Set.mem_iUnion₂.1 ha
    obtain ⟨y2, hy2, hb'⟩ := Set.mem_iUnion₂.1 hb
    have key := walk_prop (s := B w) (G' := G')
      (fun z => ∀ (hz : z ∈ B w) c (hc : c ∈ C z), (G.induce U).Reachable ⟨a, ha⟩ ⟨c, hsub z hz hc⟩)
      (hBc w).preconnected hy1
      (fun _ c hc => reach_in (hsub y1 hy1) (hCc y1) ha' hc)
      (by
        intro y z hy hz hyz hPy _ c hc
        obtain ⟨u', hu', v', hv', huv⟩ := hCa y z hyz
        refine (hPy hy u' hu').trans (Reachable.trans ?_ (reach_in (hsub z hz) (hCc z) hv' hc))
        exact Adj.reachable (by simpa using huv))
    exact key y2 hy2 hy2 b hb'
  · rw [Set.disjoint_left]
    intro a ha hb
    obtain ⟨y1, hy1, ha'⟩ := Set.mem_iUnion₂.1 ha
    obtain ⟨y2, hy2, hb'⟩ := Set.mem_iUnion₂.1 hb
    have hne : y1 ≠ y2 := fun h => Set.disjoint_left.1 (hBd w1 w2 hw) hy1 (h ▸ hy2)
    exact Set.disjoint_left.1 (hCd y1 y2 hne) ha' hb'
  · obtain ⟨y1, hy1, y2, hy2, hy⟩ := hBa w1 w2 hw
    obtain ⟨u, hu, v, hv, huv⟩ := hCa y1 y2 hy
    exact ⟨u, Set.mem_biUnion hy1 hu, v, Set.mem_biUnion hy2 hv, huv⟩

lemma sing {V : Type*} (G : SimpleGraph V) (v : V) : (G.induce {v}).Connected := by
  have := (Walk.nil : G.Walk v v).connected_induce_support
  have e : {y | y ∈ (Walk.nil : G.Walk v v).support} = {v} := by ext; simp
  rwa [e] at this

/-- Subgraph is a minor. -/
lemma minor_of_le {V : Type*} {G' G : SimpleGraph V} (h : G' ≤ G) : IsMinor G' G :=
  ⟨fun y => {y}, fun y => sing G y, fun a b hab => by simpa using hab,
    fun a b hab => ⟨a, rfl, b, rfl, h hab⟩⟩

end DiracK4


namespace DMey
open HadwigerConj SimpleGraph DiracK4

variable {V : Type*}

def Indep (G : SimpleGraph V) (I : Set V) : Prop := ∀ a ∈ I, ∀ b ∈ I, ¬ G.Adj a b

/-- invariants of the greedy construction -/
structure Inv (G : SimpleGraph V) (v : V) (D I : Set V) : Prop where
  vD : v ∈ D
  DC : ∀ d ∈ D, G.Reachable v d
  conn : (G.induce D).Connected
  ID : I ⊆ D
  ind : Indep G I
  card : D.ncard + 1 ≤ 2 * I.ncard

lemma inv_init (G : SimpleGraph V) (v : V) : Inv G v {v} {v} where
  vD := rfl
  DC := fun d hd => by rw [Set.mem_singleton_iff.1 hd]
  conn := sing G v
  ID := le_rfl
  ind := fun a ha b hb => by
    rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]; exact G.loopless.irrefl v
  card := by simp

lemma greedy [Finite V] (G : SimpleGraph V) (v : V) : ∃ D I, Inv G v D I ∧
    ∀ w, G.Reachable v w → w ∉ D → ∃ d ∈ D, G.Adj w d := by
  suffices ∀ m D I, Inv G v D I → {w | G.Reachable v w ∧ w ∉ D}.ncard = m →
      ∃ D I, Inv G v D I ∧ ∀ w, G.Reachable v w → w ∉ D → ∃ d ∈ D, G.Adj w d from
    this _ _ _ (inv_init G v) rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro D I hinv hm
  by_cases hdom : ∀ w, G.Reachable v w → w ∉ D → ∃ d ∈ D, G.Adj w d
  · exact ⟨D, I, hinv, hdom⟩
  push Not at hdom
  obtain ⟨w, hvw, hwD, hw⟩ := hdom
  -- closed neighbourhood of D
  set N : Set V := {x | x ∈ D ∨ ∃ d ∈ D, G.Adj x d} with hN
  obtain ⟨p⟩ := hvw
  have hwN : w ∉ N := by
    rintro (h | ⟨d, hd, h⟩)
    · exact hwD h
    · exact hw d hd h
  obtain ⟨dt, -, hy, hz⟩ := p.exists_boundary_dart N (Or.inl hinv.vD) hwN
  set y := dt.fst
  set z := dt.snd
  have hyz : G.Adj y z := dt.adj
  have hzD : z ∉ D := fun h => hz (Or.inl h)
  have hzD' : ∀ d ∈ D, ¬ G.Adj z d := fun d hd h => hz (Or.inr ⟨d, hd, h⟩)
  have hyD : y ∉ D := fun h => hzD' y h hyz.symm
  obtain ⟨d, hd, hyd⟩ : ∃ d ∈ D, G.Adj y d := by
    rcases hy with h | h
    · exact absurd h hyD
    · exact h
  have hry : G.Reachable v y := (hinv.DC d hd).trans (Adj.reachable hyd.symm)
  have hrz : G.Reachable v z := hry.trans (Adj.reachable hyz)
  have hyz' : y ≠ z := G.ne_of_adj hyz
  have hinv' : Inv G v (D ∪ {y, z}) (I ∪ {z}) := by
    refine ⟨Or.inl hinv.vD, ?_, ?_, ?_, ?_, ?_⟩
    · rintro e (he | he)
      · exact hinv.DC e he
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
        rcases he with rfl | rfl
        · exact hry
        · exact hrz
    · exact connected_induce_union hinv.conn.preconnected
        (induce_pair_connected_of_adj hyz).preconnected hd (by simp) hyd.symm
    · exact Set.union_subset_union hinv.ID (by simp)
    · rintro a (ha | ha) b (hb | hb)
      · exact hinv.ind a ha b hb
      · rw [Set.mem_singleton_iff.1 hb]; exact fun h => hzD' a (hinv.ID ha) h.symm
      · rw [Set.mem_singleton_iff.1 ha]; exact hzD' b (hinv.ID hb)
      · rw [Set.mem_singleton_iff.1 ha, Set.mem_singleton_iff.1 hb]; exact G.loopless.irrefl z
    · have h1 : (D ∪ {y, z}).ncard = D.ncard + 2 := by
        rw [Set.ncard_union_eq _ (Set.toFinite _) (Set.toFinite _), Set.ncard_pair hyz']
        rw [Set.disjoint_right]
        intro e he; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
        rcases he with rfl | rfl
        · exact hyD
        · exact hzD
      have h2 : (I ∪ {z}).ncard = I.ncard + 1 := by
        rw [Set.union_singleton, Set.ncard_insert_of_notMem (fun h => hzD (hinv.ID h))
          (Set.toFinite _)]
      have := hinv.card
      omega
  refine ih _ ?_ _ _ hinv' rfl
  rw [← hm]
  apply Set.ncard_lt_ncard _ (Set.toFinite _)
  refine ⟨fun e ⟨he1, he2⟩ => ⟨he1, fun h => he2 (Or.inl h)⟩, fun h => ?_⟩
  have := h ⟨hrz, hzD⟩
  exact this.2 (Or.inr (by simp))

end DMey


namespace DMey
open HadwigerConj SimpleGraph DiracK4

variable {V : Type*}

lemma conn_lift (G : SimpleGraph V) (S : Set V) (B : Set S) (h : ((G.induce S).induce B).Connected) :
    (G.induce (Subtype.val '' B)).Connected := by
  let f : (G.induce S).induce B →g G.induce (Subtype.val '' B) :=
    { toFun := fun y => ⟨y.1.1, y.1, y.2, rfl⟩
      map_rel' := fun {a b} hab => by simpa using hab }
  refine h.map f ?_
  rintro ⟨y, z, hz, rfl⟩
  exact ⟨⟨z, hz⟩, rfl⟩

lemma lift (G : SimpleGraph V) (S : Set V) (t : ℕ)
    (h : HasCompleteMinor (G.induce S) t) : HasCompleteMinor G t := by
  obtain ⟨B, hc, hd, ha⟩ := h
  refine ⟨fun w => Subtype.val '' B w, fun w => conn_lift G S _ (hc w), fun a b hab => ?_,
    fun a b hab => ?_⟩
  · exact (Set.disjoint_image_iff Subtype.val_injective).2 (hd a b hab)
  · obtain ⟨u, hu, v, hv, huv⟩ := ha a b hab
    exact ⟨u.1, ⟨u, hu, rfl⟩, v.1, ⟨v, hv, rfl⟩, huv⟩

/-- adding a connected set dominating `S` to a complete minor of `G[S]` -/
lemma cone2 {G : SimpleGraph V} (D S : Set V) (hD : (G.induce D).Connected)
    (hDS : Disjoint D S) (hdom : ∀ w ∈ S, ∃ d ∈ D, G.Adj w d) (t : ℕ)
    (h : HasCompleteMinor (G.induce S) t) : HasCompleteMinor G (t + 1) := by
  obtain ⟨B, hc, hd, ha⟩ := h
  have hx : ∀ i, Disjoint D (Subtype.val '' B i) := by
    intro i
    rw [Set.disjoint_left]
    rintro a haD ⟨y, -, rfl⟩
    exact Set.disjoint_left.1 hDS haD y.2
  have hne : ∀ i, ∃ y ∈ Subtype.val '' B i, ∃ d ∈ D, G.Adj d y := by
    intro i
    obtain ⟨⟨y, hy⟩⟩ := (hc i).nonempty
    obtain ⟨d, hd, hyd⟩ := hdom y.1 y.2
    exact ⟨y.1, ⟨y, hy, rfl⟩, d, hd, hyd.symm⟩
  refine ⟨Fin.cons D (fun i => Subtype.val '' B i), fun i => ?_, fun i j hij => ?_,
    fun i j hij => ?_⟩
  · induction i using Fin.cases with
    | zero => rw [Fin.cons_zero]; exact hD
    | succ i => rw [Fin.cons_succ]; exact conn_lift G S _ (hc i)
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd rfl hij
      | succ j => simpa using hx j
    | succ i =>
      induction j using Fin.cases with
      | zero => simpa using (hx i).symm
      | succ j =>
        simp only [Fin.cons_succ]
        exact (Set.disjoint_image_iff Subtype.val_injective).2
          (hd i j (fun h => hij (h ▸ rfl)))
  · induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd hij (by simp)
      | succ j =>
        obtain ⟨y, hy, d, hd, hdy⟩ := hne j
        refine ⟨d, ?_, y, ?_, hdy⟩
        · rw [Fin.cons_zero]; exact hd
        · rw [Fin.cons_succ]; exact hy
    | succ i =>
      induction j using Fin.cases with
      | zero =>
        obtain ⟨y, hy, d, hd, hdy⟩ := hne i
        refine ⟨y, ?_, d, ?_, hdy.symm⟩
        · rw [Fin.cons_succ]; exact hy
        · rw [Fin.cons_zero]; exact hd
      | succ j =>
        obtain ⟨u, hu, v, hv, huv⟩ := ha i j (by simpa using hij)
        refine ⟨u.1, ?_, v.1, ?_, huv⟩
        · rw [Fin.cons_succ]; exact ⟨u, hu, rfl⟩
        · rw [Fin.cons_succ]; exact ⟨v, hv, rfl⟩

lemma indep_img (G : SimpleGraph V) (S : Set V) (I : Set S) (h : Indep (G.induce S) I) :
    Indep G (Subtype.val '' I) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  exact fun hab => h a ha b hb (by simpa using hab)

end DMey


namespace DHalf
open HadwigerConj SimpleGraph DiracK4 DMey

theorem claim : ∀ n (V : Type) [Finite V] (G : SimpleGraph V) (s : ℕ), Nat.card V = n →
    ¬ HasCompleteMinor G (s + 1) →
    ∃ S : Set V, ∃ col : V → Fin s, n ≤ 2 * S.ncard ∧
      ∀ a ∈ S, ∀ b ∈ S, G.Adj a b → col a ≠ col b := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G s hn hno
  classical
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · cases s with
    | zero =>
      have : IsEmpty V := Finite.card_eq_zero_iff.1 (hn.trans h0)
      exact ⟨∅, isEmptyElim, by omega, fun a ha => ha.elim⟩
    | succ s => exact ⟨∅, fun _ => 0, by omega, fun a ha => ha.elim⟩
  have : Nonempty V := Nat.card_pos_iff.1 (hn ▸ hpos) |>.1
  obtain ⟨v⟩ := this
  cases s with
  | zero =>
    exact absurd ⟨fun _ => {v}, fun _ => sing G v, fun a b h => absurd (Fin.subsingleton_one.elim a b) h,
      fun a b h => absurd (Fin.subsingleton_one.elim a b) (by simpa using h)⟩ hno
  | succ s =>
  obtain ⟨D, ID, hinv, hdom⟩ := greedy G v
  set C : Set V := {w | G.Reachable v w} with hC
  set S1 : Set V := C \ D with hS1
  set S2 : Set V := Cᶜ with hS2
  have hcard : ∀ S : Set V, v ∉ S → Nat.card S < n := by
    intro S hv
    rw [← hn, Nat.card_coe_set_eq, ← Set.ncard_univ]
    exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.2 (fun h => hv (h ▸ Set.mem_univ v)))
      (Set.toFinite _)
  obtain ⟨T1, col1, hc1, hp1⟩ := ih _ (hcard S1 (fun h => h.2 hinv.vD)) S1 (G.induce S1) s rfl
    (fun h => hno (cone2 D S1 hinv.conn Set.disjoint_sdiff_right
      (fun w hw => hdom w hw.1 hw.2) _ h))
  obtain ⟨T2, col2, hc2, hp2⟩ := ih _ (hcard S2 (fun h => h (Reachable.refl v))) S2
    (G.induce S2) (s + 1) rfl (fun h => hno (lift G S2 _ h))
  set J1 := Subtype.val '' T1
  set J2 := Subtype.val '' T2
  have hDC : D ⊆ C := fun x hx => hinv.DC x hx
  have hnoedge : ∀ a ∈ C, ∀ b ∈ S2, ¬ G.Adj a b := by
    intro a ha b hb hab
    exact hb (Reachable.trans ha (Adj.reachable hab))
  let col : V → Fin (s + 1) := fun a =>
    if h : a ∈ S1 then Fin.castSucc (col1 ⟨a, h⟩)
    else if a ∈ C then Fin.last s
    else if h2 : a ∈ S2 then col2 ⟨a, h2⟩ else 0
  have hJ1 : J1 ⊆ S1 := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hJ2 : J2 ⊆ S2 := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hID : ID ⊆ D := hinv.ID
  have col_J1 : ∀ a (h : a ∈ S1), col a = Fin.castSucc (col1 ⟨a, h⟩) := by
    intro a h; simp only [col, dif_pos h]
  have col_ID : ∀ a ∈ D, col a = Fin.last s := by
    intro a h
    have h1 : a ∉ S1 := fun h' => h'.2 h
    simp only [col, dif_neg h1, if_pos (hDC h)]
  have col_J2 : ∀ a (h : a ∈ S2), col a = col2 ⟨a, h⟩ := by
    intro a h
    have h1 : a ∉ S1 := fun h' => h h'.1
    have h2 : a ∉ C := h
    simp only [col, dif_neg h1, if_neg h2, dif_pos h]
  refine ⟨J1 ∪ ID ∪ J2, col, ?_, ?_⟩
  · have d1 : Disjoint J1 ID := Set.disjoint_left.2 fun a ha hb => (hJ1 ha).2 (hID hb)
    have d2 : Disjoint (J1 ∪ ID) J2 := by
      rw [Set.disjoint_left]; rintro a (ha | ha) hb
      · exact hJ2 hb (hJ1 ha).1
      · exact hJ2 hb (hDC (hID ha))
    rw [Set.ncard_union_eq d2 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_union_eq d1 (Set.toFinite _) (Set.toFinite _),
      Set.ncard_image_of_injective _ Subtype.val_injective,
      Set.ncard_image_of_injective _ Subtype.val_injective]
    rw [Nat.card_coe_set_eq] at hc1 hc2
    have e1 : C.ncard = D.ncard + S1.ncard := by
      rw [hS1, Set.ncard_sdiff hDC (Set.toFinite _)]
      have := Set.ncard_le_ncard hDC (Set.toFinite _); omega
    have e2 : C.ncard + S2.ncard = n := by
      rw [hS2, Set.ncard_add_ncard_compl, hn]
    have := hinv.card
    omega
  · have hp1' : ∀ a ∈ J1, ∀ b ∈ J1, G.Adj a b → col a ≠ col b := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      rw [col_J1 _ x.2, col_J1 _ y.2]
      intro h
      exact hp1 x hx y hy (by simpa using hxy) (Fin.castSucc_injective _ h)
    have hp2' : ∀ a ∈ J2, ∀ b ∈ J2, G.Adj a b → col a ≠ col b := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
      rw [col_J2 _ x.2, col_J2 _ y.2]
      exact hp2 x hx y hy (by simpa using hxy)
    have h12 : ∀ a ∈ J1, ∀ b ∈ ID, col a ≠ col b := by
      intro a ha b hb
      rw [col_J1 _ (hJ1 ha), col_ID _ (hID hb)]
      exact Fin.castSucc_ne_last _
    rintro a ((ha | ha) | ha) b ((hb | hb) | hb) hab
    · exact hp1' a ha b hb hab
    · exact h12 a ha b hb
    · exact absurd hab (hnoedge a (hJ1 ha).1 b (hJ2 hb))
    · exact (h12 b hb a ha).symm
    · exact absurd hab (hinv.ind a ha b hb)
    · exact absurd hab (hnoedge a (hDC (hID ha)) b (hJ2 hb))
    · exact absurd hab.symm (hnoedge b (hJ1 hb).1 a (hJ2 ha))
    · exact absurd hab.symm (hnoedge b (hDC (hID hb)) a (hJ2 ha))
    · exact hp2' a ha b hb hab

end DHalf

open HadwigerConj in
theorem solution (t : ℕ) {V : Type} [Finite V] (G : SimpleGraph V)
    (hG : ¬ HasCompleteMinor G (t + 1)) :
    ∃ S : Set V, Nat.card V ≤ 2 * S.ncard ∧ (G.induce S).Colorable t := by
  obtain ⟨S, col, hn, hp⟩ := DHalf.claim _ V G t rfl hG
  exact ⟨S, hn, ⟨SimpleGraph.Coloring.mk (fun x => col x.1)
    (fun {a b} h => hp a.1 a.2 b.1 b.2 (by simpa using h))⟩⟩
