-- Prove2me | solution 1 for HadwigerConj.duchet_meyniel
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T20:53:12.459872+00:00
-- url     : https://prove2.me/submissions/f05ae899-d1f8-43a6-83c3-068701f27bf4

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


namespace DMey
open HadwigerConj SimpleGraph DiracK4

theorem claim : ∀ n (V : Type) [Finite V] (G : SimpleGraph V), Nat.card V = n →
    ∃ t, ∃ I : Set V, HasCompleteMinor G t ∧ Indep G I ∧ n ≤ t * (2 * I.ncard - 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ G hn
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · exact ⟨0, ∅, ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩,
      fun a ha => ha.elim, by omega⟩
  have : Nonempty V := Nat.card_pos_iff.1 (hn ▸ hpos) |>.1
  obtain ⟨v⟩ := this
  obtain ⟨D, ID, hinv, hdom⟩ := greedy G v
  set C : Set V := {w | G.Reachable v w} with hC
  set S1 : Set V := C \ D with hS1
  set S2 : Set V := Cᶜ with hS2
  have hcard : ∀ S : Set V, v ∉ S → Nat.card S < n := by
    intro S hv
    rw [← hn, Nat.card_coe_set_eq, ← Set.ncard_univ]
    exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.2 (fun h => hv (h ▸ Set.mem_univ v)))
      (Set.toFinite _)
  obtain ⟨t1, I1, hm1, hi1, hc1⟩ := ih _ (hcard S1 (fun h => h.2 hinv.vD)) S1 (G.induce S1) rfl
  obtain ⟨t2, I2, hm2, hi2, hc2⟩ := ih _ (hcard S2 (fun h => h (Reachable.refl v))) S2
    (G.induce S2) rfl
  have hM1 : HasCompleteMinor G (t1 + 1) :=
    cone2 D S1 hinv.conn Set.disjoint_sdiff_right (fun w hw => hdom w hw.1 hw.2) t1 hm1
  have hM2 : HasCompleteMinor G t2 := lift G S2 t2 hm2
  set J1 := Subtype.val '' I1
  set J2 := Subtype.val '' I2
  have hJ1 : Indep G J1 := indep_img G S1 I1 hi1
  have hJ2 : Indep G J2 := indep_img G S2 I2 hi2
  have eJ1 : J1.ncard = I1.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have eJ2 : J2.ncard = I2.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  -- an independent set inside `C` at least as large as `ID` and `J1`
  obtain ⟨J, hJC, hJ, hJa, hJb⟩ : ∃ J : Set V, J ⊆ C ∧ Indep G J ∧ ID.ncard ≤ J.ncard ∧
      J1.ncard ≤ J.ncard := by
    by_cases hle : ID.ncard ≤ J1.ncard
    · refine ⟨J1, ?_, hJ1, hle, le_rfl⟩
      rintro _ ⟨y, -, rfl⟩; exact y.2.1
    · exact ⟨ID, fun x hx => hinv.DC x (hinv.ID hx), hinv.ind, le_rfl, by omega⟩
  have hJ2C : J2 ⊆ S2 := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hnoedge : ∀ a ∈ C, ∀ b ∈ S2, ¬ G.Adj a b := by
    intro a ha b hb hab
    exact hb (Reachable.trans ha (Adj.reachable hab))
  have hI : Indep G (J ∪ J2) := by
    rintro a (ha | ha) b (hb | hb)
    · exact hJ a ha b hb
    · exact hnoedge a (hJC ha) b (hJ2C hb)
    · exact fun h => hnoedge b (hJC hb) a (hJ2C ha) h.symm
    · exact hJ2 a ha b hb
  have hdisj : Disjoint J J2 := by
    rw [Set.disjoint_left]; intro a ha hb; exact hJ2C hb (hJC ha)
  have eI : (J ∪ J2).ncard = J.ncard + J2.ncard :=
    Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)
  -- vertex count
  have hsplit : n = D.ncard + S1.ncard + S2.ncard := by
    have hDC : D ⊆ C := fun x hx => hinv.DC x hx
    have e1 : C.ncard = D.ncard + S1.ncard := by
      rw [hS1, Set.ncard_sdiff hDC (Set.toFinite _)]
      have := Set.ncard_le_ncard hDC (Set.toFinite _); omega
    have e2 : C.ncard + S2.ncard = n := by
      rw [hS2, Set.ncard_add_ncard_compl, hn]
    omega
  rw [Nat.card_coe_set_eq] at hc1 hc2
  have hDcard := hinv.card
  set a := J.ncard
  set b := I2.ncard
  have ha1 : 1 ≤ a := by
    have : 1 ≤ ID.ncard := by omega
    omega
  set T := max (t1 + 1) t2 with hTdef
  have hMT : HasCompleteMinor G T := by
    rw [hTdef]
    rcases le_total (t1 + 1) t2 with h | h
    · rw [max_eq_right h]; exact hM2
    · rw [max_eq_left h]; exact hM1
  refine ⟨T, J ∪ J2, hMT, hI, ?_⟩
  rw [eI, eJ2]
  -- arithmetic
  obtain ⟨A, hA⟩ : ∃ A, 2 * a - 1 = A ∧ 2 * a = A + 1 := ⟨2 * a - 1, rfl, by omega⟩
  have h1 : S1.ncard ≤ t1 * A := by
    refine hc1.trans (Nat.mul_le_mul_left _ ?_); omega
  have hCle : D.ncard + S1.ncard ≤ (t1 + 1) * A := by
    have : D.ncard ≤ A := by omega
    nlinarith
  have hT1 : (t1 + 1) * A ≤ T * A := Nat.mul_le_mul_right _ (le_max_left _ _)
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · rw [hb0] at hc2 ⊢
    simp at hc2
    have : 2 * (a + 0) - 1 = A := by omega
    rw [this]; omega
  · obtain ⟨B, hB⟩ : ∃ B, 2 * b - 1 = B ∧ 2 * b = B + 1 := ⟨2 * b - 1, rfl, by omega⟩
    rw [hB.1] at hc2
    have hT2 : t2 * B ≤ T * B := Nat.mul_le_mul_right _ (le_max_right _ _)
    have : 2 * (a + b) - 1 = A + B + 1 := by omega
    rw [this]
    nlinarith

end DMey

open HadwigerConj in
theorem solution {V : Type} [Finite V] (G : SimpleGraph V) :
    ∃ t : ℕ, HasCompleteMinor G t ∧
      (Nat.card V : ℝ) / (2 * (G.indepNum : ℝ) - 1) ≤ t := by
  obtain ⟨t, I, hM, hI, hn⟩ := DMey.claim _ V G rfl
  refine ⟨t, hM, ?_⟩
  have hfin := Set.toFinite I
  have hind : G.IsIndepSet (hfin.toFinset : Set V) := by
    rw [Set.Finite.coe_toFinset]
    intro a ha b hb _
    exact hI a ha b hb
  have hle : I.ncard ≤ G.indepNum := by
    rw [Set.ncard_eq_toFinset_card I hfin]; exact hind.card_le_indepNum
  rcases Nat.eq_zero_or_pos (Nat.card V) with h0 | hpos
  · rw [h0]; simp
  · have hI1 : 1 ≤ I.ncard := by
      by_contra h; push Not at h
      have : 2 * I.ncard - 1 = 0 := by omega
      rw [this] at hn; omega
    have hα : (1 : ℝ) ≤ G.indepNum := by exact_mod_cast hI1.trans hle
    rw [div_le_iff₀ (by linarith)]
    have hcast : ((2 * I.ncard - 1 : ℕ) : ℝ) = 2 * (I.ncard : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have h1 : (Nat.card V : ℝ) ≤ t * (2 * (I.ncard : ℝ) - 1) := by
      rw [← hcast]; exact_mod_cast hn
    have h2 : (I.ncard : ℝ) ≤ G.indepNum := by exact_mod_cast hle
    have ht : (0 : ℝ) ≤ t := by positivity
    nlinarith
