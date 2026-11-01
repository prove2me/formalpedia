-- Prove2me | solution 1 for HadwigerConj.kostochka_thomason_colorable
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T21:34:21.052201+00:00
-- url     : https://prove2.me/submissions/39edfc15-281d-4ab9-87aa-abebb4c8db48

import Mathlib
import Definitions.Def_HadwigerConj_Defs

set_option autoImplicit false

namespace KTLib
open HadwigerConj SimpleGraph

section minors
variable {U W V : Type*}

lemma reach_sub (G : SimpleGraph V) {s t : Set V} (hst : s ⊆ t) {a b : V} (ha : a ∈ s) (hb : b ∈ s)
    (h : (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩) : (G.induce t).Reachable ⟨a, hst ha⟩ ⟨b, hst hb⟩ :=
  h.map (induceHomOfLE G hst).toHom

lemma induce_biUnion_connected (G : SimpleGraph V) (G' : SimpleGraph W) (B : W → Set V)
    (hB : ∀ x, (G.induce (B x)).Connected)
    (hadj : ∀ x y, G'.Adj x y → ∃ u ∈ B x, ∃ v ∈ B y, G.Adj u v)
    (S : Set W) (hS : (G'.induce S).Connected) :
    (G.induce (⋃ x ∈ S, B x)).Connected := by
  set T := ⋃ x ∈ S, B x with hT
  have sub : ∀ x ∈ S, B x ⊆ T := fun x hx _ hp => Set.mem_biUnion hx hp
  have key : ∀ (a b : S) (_ : (G'.induce S).Walk a b) (p q : V) (hp : p ∈ B a) (hq : q ∈ B b),
      (G.induce T).Reachable ⟨p, sub a a.2 hp⟩ ⟨q, sub b b.2 hq⟩ := by
    intro a b w
    induction w with
    | @nil a =>
      intro p q hp hq
      exact reach_sub G (sub _ a.2) hp hq ((hB _).preconnected ⟨p, hp⟩ ⟨q, hq⟩)
    | @cons a c b h w ih =>
      intro p q hp hq
      obtain ⟨p', hp', q', hq', hpq⟩ := hadj a.1 c.1 h
      have r1 := reach_sub G (sub _ a.2) hp hp' ((hB _).preconnected ⟨p, hp⟩ ⟨p', hp'⟩)
      have r2 : (G.induce T).Reachable ⟨p', sub _ a.2 hp'⟩ ⟨q', sub _ c.2 hq'⟩ :=
        SimpleGraph.Adj.reachable (show G.Adj p' q' from hpq)
      exact r1.trans (r2.trans (ih q' q hq' hq))
  obtain ⟨⟨x0, hx0⟩⟩ := hS.nonempty
  obtain ⟨⟨u0, hu0⟩⟩ := (hB x0).nonempty
  rw [connected_iff]
  refine ⟨?_, ⟨⟨u0, sub x0 hx0 hu0⟩⟩⟩
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  have hp' := hp; have hq' := hq
  rw [hT, Set.mem_iUnion₂] at hp' hq'
  obtain ⟨a, ha, hpa⟩ := hp'
  obtain ⟨b, hb, hqb⟩ := hq'
  obtain ⟨w⟩ := hS.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  exact key ⟨a, ha⟩ ⟨b, hb⟩ w p q hpa hqb

theorem isMinor_trans {H : SimpleGraph U} {G' : SimpleGraph W} {G : SimpleGraph V}
    (h1 : IsMinor H G') (h2 : IsMinor G' G) : IsMinor H G := by
  obtain ⟨B2, c2, d2, a2⟩ := h1
  obtain ⟨B1, c1, d1, a1⟩ := h2
  refine ⟨fun w => ⋃ x ∈ B2 w, B1 x, fun w => induce_biUnion_connected G G' B1 c1 a1 _ (c2 w),
    ?_, ?_⟩
  · intro w1 w2 hne
    rw [Set.disjoint_left]
    intro v hv1 hv2
    rw [Set.mem_iUnion₂] at hv1 hv2
    obtain ⟨x, hx, hvx⟩ := hv1
    obtain ⟨y, hy, hvy⟩ := hv2
    have hxy : x ≠ y := fun h => (Set.disjoint_left.mp (d2 w1 w2 hne)) hx (h ▸ hy)
    exact Set.disjoint_left.mp (d1 x y hxy) hvx hvy
  · intro w1 w2 hadj
    obtain ⟨x, hx, y, hy, hxy⟩ := a2 w1 w2 hadj
    obtain ⟨u, hu, v, hv, huv⟩ := a1 x y hxy
    exact ⟨u, Set.mem_biUnion hx hu, v, Set.mem_biUnion hy hv, huv⟩

lemma induce_singleton_conn (G : SimpleGraph V) (a : V) : (G.induce {a}).Connected := by
  rw [connected_iff]
  refine ⟨fun p q => ?_, ⟨⟨a, rfl⟩⟩⟩
  have : p = q := Subtype.ext (p.2.trans q.2.symm)
  rw [this]

theorem isMinor_of_hom {G' : SimpleGraph W} {G : SimpleGraph V} (f : G' →g G)
    (hf : Function.Injective f) : IsMinor G' G :=
  ⟨fun x => {f x}, fun x => induce_singleton_conn G (f x),
    fun x y hne => Set.disjoint_singleton.mpr (hf.ne hne),
    fun x y h => ⟨f x, rfl, f y, rfl, f.map_adj h⟩⟩

theorem hasCompleteMinor_of_isMinor {G' : SimpleGraph W} {G : SimpleGraph V} {s : ℕ}
    (h : HasCompleteMinor G' s) (h2 : IsMinor G' G) : HasCompleteMinor G s :=
  isMinor_trans h h2

theorem hasCompleteMinor_mono {G' G : SimpleGraph V} {s : ℕ} (h : HasCompleteMinor G' s)
    (hle : G' ≤ G) : HasCompleteMinor G s :=
  hasCompleteMinor_of_isMinor h (isMinor_of_hom ⟨id, fun h => hle h⟩ Function.injective_id)

/-- lift a minor of an induced subgraph, remembering the branch sets lie in `S`. -/
theorem minor_induce_lift {H : SimpleGraph W} (G : SimpleGraph V) (S : Set V)
    (h : IsMinor H (G.induce S)) :
    ∃ B : W → Set V, (∀ w, B w ⊆ S) ∧ (∀ w, (G.induce (B w)).Connected) ∧
      (∀ w₁ w₂, w₁ ≠ w₂ → Disjoint (B w₁) (B w₂)) ∧
      (∀ w₁ w₂, H.Adj w₁ w₂ → ∃ u ∈ B w₁, ∃ v ∈ B w₂, G.Adj u v) := by
  obtain ⟨B, c, d, a⟩ := h
  refine ⟨fun w => Subtype.val '' B w, fun w => ?_, fun w => ?_, fun w₁ w₂ hne => ?_, fun w₁ w₂ hadj => ?_⟩
  · rintro _ ⟨x, _, rfl⟩; exact x.2
  · let φ : (G.induce S).induce (B w) →g G.induce (Subtype.val '' B w) :=
      ⟨fun x => ⟨x.1.1, x.1, x.2, rfl⟩, fun h => h⟩
    refine (c w).map φ ?_
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have : y = x := Subtype.ext hxy
    exact Set.disjoint_left.mp (d w₁ w₂ hne) hx (this ▸ hy)
  · obtain ⟨u, hu, v, hv, huv⟩ := a w₁ w₂ hadj
    exact ⟨u.1, ⟨u, hu, rfl⟩, v.1, ⟨v, hv, rfl⟩, huv⟩

/-- cone: a `K_s` minor inside the neighbourhood of `v` plus `{v}` gives `K_{s+1}`. -/
theorem cone_minor (G : SimpleGraph V) (v : V) (s : ℕ)
    (h : HasCompleteMinor (G.induce (G.neighborSet v)) s) : HasCompleteMinor G (s + 1) := by
  obtain ⟨B, hsub, c, d, a⟩ := minor_induce_lift G _ h
  have hne : ∀ i, (B i).Nonempty := fun i => by
    obtain ⟨⟨x, hx⟩⟩ := (c i).nonempty; exact ⟨x, hx⟩
  have hv : ∀ i, v ∉ B i := fun i hvi => G.irrefl (hsub i hvi)
  obtain ⟨F, hF⟩ : ∃ F : Fin (s + 1) → Set V,
      ∀ i, F i = if h : i.1 < s then B ⟨i.1, h⟩ else {v} := ⟨_, fun _ => rfl⟩
  have Flt : ∀ i (h : i.1 < s), F i = B ⟨i.1, h⟩ := fun i h => by rw [hF, dif_pos h]
  have Fge : ∀ i, ¬ i.1 < s → F i = {v} := fun i h => by rw [hF, dif_neg h]
  refine ⟨F, fun i => ?_, fun i j hij => ?_, fun i j hij => ?_⟩
  · by_cases h : i.1 < s
    · rw [Flt i h]; exact c _
    · rw [Fge i h]; exact induce_singleton_conn G v
  · have hij' : i.1 ≠ j.1 := fun e => hij (Fin.ext e)
    by_cases hi : i.1 < s <;> by_cases hj : j.1 < s
    · rw [Flt i hi, Flt j hj]; exact d _ _ (fun e => hij' (congrArg (fun x : Fin s => x.val) e))
    · rw [Flt i hi, Fge j hj, Set.disjoint_singleton_right]; exact hv _
    · rw [Fge i hi, Flt j hj, Set.disjoint_singleton_left]; exact hv _
    · exact absurd (by omega : i.1 = j.1) hij'
  · have hij' : i.1 ≠ j.1 := fun e => ((top_adj i j).mp hij) (Fin.ext e)
    by_cases hi : i.1 < s <;> by_cases hj : j.1 < s
    · rw [Flt i hi, Flt j hj]
      exact a _ _ ((top_adj _ _).mpr (fun e => hij' (congrArg (fun x : Fin s => x.val) e)))
    · obtain ⟨x, hx⟩ := hne ⟨i.1, hi⟩
      rw [Flt i hi, Fge j hj]
      exact ⟨x, hx, v, rfl, (hsub _ hx).symm⟩
    · obtain ⟨x, hx⟩ := hne ⟨j.1, hj⟩
      rw [Fge i hi, Flt j hj]
      exact ⟨v, rfl, x, hx, hsub _ hx⟩
    · exact absurd (by omega : i.1 = j.1) hij'

end minors

section contraction
variable {V : Type*}

/-- contraction of the edge `uv` onto `{x // x ≠ v}` (`v` merged into `u`). -/
def contr (G : SimpleGraph V) (u v : V) : SimpleGraph {x : V // x ≠ v} :=
  SimpleGraph.fromRel fun x y => G.Adj x.1 y.1 ∨ (x.1 = u ∧ G.Adj v y.1)

theorem contr_isMinor (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    IsMinor (contr G u v) G := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : {x : V // x ≠ v} → Set V,
      ∀ x, B x = if x.1 = u then {u, v} else {x.1} := ⟨_, fun _ => rfl⟩
  have Bu : ∀ x : {x : V // x ≠ v}, x.1 = u → B x = {u, v} := fun x h => by rw [hB, if_pos h]
  have Bn : ∀ x : {x : V // x ≠ v}, x.1 ≠ u → B x = {x.1} := fun x h => by rw [hB, if_neg h]
  have mem : ∀ x, x.1 ∈ B x := fun x => by
    by_cases h : x.1 = u
    · rw [Bu x h]; simp [h]
    · rw [Bn x h]; rfl
  have memv : ∀ x : {x : V // x ≠ v}, x.1 = u → v ∈ B x := fun x h => by
    rw [Bu x h]; simp
  refine ⟨B, fun x => ?_, fun x y hne => ?_, fun x y hxy => ?_⟩
  · by_cases h : x.1 = u
    · rw [Bu x h]; exact induce_pair_connected_of_adj huv
    · rw [Bn x h]; exact induce_singleton_conn G _
  · have hne' : x.1 ≠ y.1 := fun h => hne (Subtype.ext h)
    by_cases hx : x.1 = u <;> by_cases hy : y.1 = u
    · exact absurd (hx.trans hy.symm) hne'
    · rw [Bu x hx, Bn y hy, Set.disjoint_singleton_right]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hne' (hx.trans h.symm), y.2⟩
    · rw [Bn x hx, Bu y hy, Set.disjoint_singleton_left]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨fun h => hne' (h.trans hy.symm), x.2⟩
    · rw [Bn x hx, Bn y hy]; exact Set.disjoint_singleton.mpr hne'
  · simp only [contr, fromRel_adj] at hxy
    obtain ⟨_, h | h⟩ := hxy
    · rcases h with h | ⟨hx, h⟩
      · exact ⟨x.1, mem x, y.1, mem y, h⟩
      · exact ⟨v, memv x hx, y.1, mem y, h⟩
    · rcases h with h | ⟨hy, h⟩
      · exact ⟨x.1, mem x, y.1, mem y, h.symm⟩
      · exact ⟨x.1, mem x, v, memv y hy, h.symm⟩

theorem edge_count_lower [Finite V] (G : SimpleGraph V) (v u : V) (huv : u ≠ v)
    (C : SimpleGraph {x : V // x ≠ v})
    (hC : ∀ x y : {x : V // x ≠ v}, G.Adj x.1 y.1 → C.Adj x y)
    (T : Set V) (hT : ∀ w ∈ T, ∃ hw : w ≠ v, C.Adj ⟨u, huv⟩ ⟨w, hw⟩ ∧ ¬ G.Adj u w) :
    G.edgeSet.ncard + T.ncard ≤ C.edgeSet.ncard + (G.neighborSet v).ncard := by
  classical
  set f : Sym2 {x : V // x ≠ v} → Sym2 V := Sym2.map Subtype.val with hf
  have finj : Function.Injective f := Sym2.map.injective Subtype.val_injective
  set X := G.edgeSet \ G.incidenceSet v with hX
  set Y := (fun w => s(u, w)) '' T with hY
  have hXY : X ∪ Y ⊆ f '' C.edgeSet := by
    rintro e (he | he)
    · rw [hX, Set.mem_sdiff] at he
      obtain ⟨he1, he2⟩ := he
      induction e using Sym2.ind with
      | _ a b =>
        have ha : a ≠ v := fun h => he2 ⟨he1, by simp [h]⟩
        have hb : b ≠ v := fun h => he2 ⟨he1, by simp [h]⟩
        refine ⟨s(⟨a, ha⟩, ⟨b, hb⟩), ?_, by simp [hf]⟩
        exact hC ⟨a, ha⟩ ⟨b, hb⟩ he1
    · obtain ⟨w, hw, rfl⟩ := he
      obtain ⟨hwv, hCw, _⟩ := hT w hw
      exact ⟨s(⟨u, huv⟩, ⟨w, hwv⟩), hCw, by simp [hf]⟩
  have hdisj : Disjoint X Y := by
    rw [Set.disjoint_left]
    rintro e he ⟨w, hw, rfl⟩
    exact (hT w hw).2.2 (he.1 : G.Adj u w)
  have hYc : Y.ncard = T.ncard :=
    Set.ncard_image_of_injective _ (fun a b h => Sym2.congr_right.mp h)
  have hinc : G.incidenceSet v ⊆ (fun w => s(v, w)) '' G.neighborSet v := by
    intro e ⟨he1, he2⟩
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp he2
    exact ⟨w, he1, rfl⟩
  have h1 : (G.incidenceSet v).ncard ≤ (G.neighborSet v).ncard :=
    (Set.ncard_le_ncard hinc).trans (Set.ncard_image_le)
  have h2 : G.edgeSet.ncard ≤ X.ncard + (G.incidenceSet v).ncard :=
    Set.ncard_le_ncard_sdiff_add_ncard _ _
  have h3 : (X ∪ Y).ncard = X.ncard + Y.ncard := Set.ncard_union_eq hdisj
  have h4 : (X ∪ Y).ncard ≤ (f '' C.edgeSet).ncard := Set.ncard_le_ncard hXY
  have h5 : (f '' C.edgeSet).ncard = C.edgeSet.ncard := Set.ncard_image_of_injective _ finj
  omega

theorem contr_edges [Finite V] (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    G.edgeSet.ncard + (G.neighborSet v).ncard ≤
      (contr G u v).edgeSet.ncard + (G.neighborSet v).ncard + 1 +
        (G.neighborSet u ∩ G.neighborSet v).ncard := by
  classical
  have hne : u ≠ v := huv.ne
  set T := G.neighborSet v \ insert u (G.neighborSet u) with hT
  have key := edge_count_lower G v u hne (contr G u v)
    (fun x y h => by
      rw [contr, fromRel_adj]
      exact ⟨fun e => h.ne (congrArg Subtype.val e), Or.inl (Or.inl h)⟩) T
    (fun w hw => by
      rw [hT, Set.mem_sdiff, Set.mem_insert_iff, not_or] at hw
      obtain ⟨hw1, hw2, hw3⟩ := hw
      refine ⟨(G.ne_of_adj hw1).symm, ?_, hw3⟩
      rw [contr, fromRel_adj]
      exact ⟨fun e => hw2 (congrArg Subtype.val e).symm, Or.inl (Or.inr ⟨rfl, hw1⟩)⟩)
  have hsub : G.neighborSet v ⊆ T ∪ insert u (G.neighborSet u ∩ G.neighborSet v) := by
    intro w hw
    by_cases h : w ∈ insert u (G.neighborSet u)
    · right
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hw⟩
    · left; exact ⟨hw, h⟩
  have c1 := Set.ncard_le_ncard hsub
  have c2 := Set.ncard_union_le T (insert u (G.neighborSet u ∩ G.neighborSet v))
  have c3 := Set.ncard_insert_le u (G.neighborSet u ∩ G.neighborSet v)
  omega

/-- deletion of `v`. -/
def del (G : SimpleGraph V) (v : V) : SimpleGraph {x : V // x ≠ v} := G.comap Subtype.val

theorem del_isMinor (G : SimpleGraph V) (v : V) : IsMinor (del G v) G :=
  isMinor_of_hom ⟨Subtype.val, fun h => h⟩ Subtype.val_injective

theorem del_edges [Finite V] (G : SimpleGraph V) (v u : V) (huv : u ≠ v) :
    G.edgeSet.ncard ≤ (del G v).edgeSet.ncard + (G.neighborSet v).ncard := by
  have := edge_count_lower G v u huv (del G v) (fun x y h => h) ∅ (fun w hw => absurd hw id)
  simpa using this

end contraction

section extremal
variable {V : Type*}

theorem card_ne [Finite V] (v : V) : Nat.card {x : V // x ≠ v} = Nat.card V - 1 := by
  classical
  letI := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_subtype_eq,
    Nat.card_eq_fintype_card]

theorem exists_deg_le [Finite V] [Nonempty V] (G : SimpleGraph V) :
    ∃ v, Nat.card V * (G.neighborSet v).ncard ≤ 2 * G.edgeSet.ncard := by
  classical
  letI := Fintype.ofFinite V
  have hs := G.sum_degrees_eq_twice_card_edges
  obtain ⟨v, -, hv⟩ := Finset.exists_min_image Finset.univ (fun v => G.degree v) Finset.univ_nonempty
  refine ⟨v, ?_⟩
  have hdeg : ∀ w, (G.neighborSet w).ncard = G.degree w := fun w => by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
  have hE : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']; rfl
  rw [hdeg, hE, ← hs, Nat.card_eq_fintype_card]
  have := Finset.card_nsmul_le_sum Finset.univ (fun w => G.degree w) (G.degree v) (fun w _ => hv w (Finset.mem_univ _))
  simpa [Finset.card_univ] using this

/-- the dense hypothesis. -/
def Dense (s : ℕ) (d : ℝ) : Prop :=
  ∀ (W : Type) [Finite W] (H : SimpleGraph W), Nonempty W → (Nat.card W : ℝ) ≤ 2 * d + 2 →
    (∀ w, d - 1 < ((H.neighborSet w).ncard : ℝ)) → HasCompleteMinor H s

theorem induce_nbr_deg {V : Type} (G : SimpleGraph V) (v : V) (w : G.neighborSet v) :
    ((G.induce (G.neighborSet v)).neighborSet w).ncard =
      (G.neighborSet w.1 ∩ G.neighborSet v).ncard := by
  have h : Subtype.val '' ((G.induce (G.neighborSet v)).neighborSet w) =
      G.neighborSet w.1 ∩ G.neighborSet v := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← h, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem extremal (s : ℕ) (d : ℝ) (hd : 0 < d) (hD : Dense s d) :
    ∀ (V : Type) [Finite V] (G : SimpleGraph V), Nonempty V → ¬ HasCompleteMinor G (s + 1) →
      (G.edgeSet.ncard : ℝ) < d * Nat.card V := by
  intro V0 _ G0 hV0 hG0
  suffices H : ∀ N, ∀ (V : Type) [Finite V], Nat.card V = N → ∀ m, ∀ (G : SimpleGraph V),
      G.edgeSet.ncard ≤ m → Nonempty V → ¬ HasCompleteMinor G (s + 1) →
      (G.edgeSet.ncard : ℝ) < d * Nat.card V from H _ V0 rfl _ G0 le_rfl hV0 hG0
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IHN =>
  intro V _ hN m
  induction m with
  | zero =>
    intro G hm hV _
    have : G.edgeSet.ncard = 0 := by omega
    rw [this]
    have : (0 : ℝ) < Nat.card V := by exact_mod_cast Nat.card_pos
    simp only [Nat.cast_zero]; positivity
  | succ m IHm =>
  intro G hm hV hG
  by_contra hlt
  push Not at hlt
  have hNpos : (1 : ℝ) ≤ Nat.card V := by exact_mod_cast Nat.card_pos
  -- case A: too many edges
  by_cases hA : d * Nat.card V + 1 ≤ G.edgeSet.ncard
  · have hpos : 0 < G.edgeSet.ncard := by
      have : (0 : ℝ) < G.edgeSet.ncard := by nlinarith
      exact_mod_cast this
    obtain ⟨e, he⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    set G' := G.deleteEdges {e}
    have hE' : G'.edgeSet.ncard + 1 = G.edgeSet.ncard := by
      rw [edgeSet_deleteEdges]; exact Set.ncard_sdiff_singleton_add_one he
    have hG' : ¬ HasCompleteMinor G' (s + 1) := fun h =>
      hG (hasCompleteMinor_mono h (deleteEdges_le _))
    have := IHm G' (by omega) hV hG'
    have hc : (G'.edgeSet.ncard : ℝ) + 1 = G.edgeSet.ncard := by exact_mod_cast hE'
    linarith
  push Not at hA
  -- case B1: an isolated vertex
  by_cases hB1 : ∃ v, (G.neighborSet v).ncard = 0
  · obtain ⟨v, hv⟩ := hB1
    by_cases hone : Nat.card V = 1
    · have hsub : Subsingleton V := (Finite.card_le_one_iff_subsingleton).mp hone.le
      have : G.edgeSet.ncard = 0 := by
        rw [Set.ncard_eq_zero (Set.toFinite _)]
        ext e
        induction e using Sym2.ind with
        | _ a b => simp [Subsingleton.elim a b]
      rw [this, hone] at hlt
      simp at hlt; linarith
    · have hN2 : 2 ≤ Nat.card V := by have := Nat.card_pos (α := V); omega
      obtain ⟨u, hu⟩ : ∃ u : V, u ≠ v := by
        by_contra hc
        push Not at hc
        have : Subsingleton V := ⟨fun a b => (hc a).trans (hc b).symm⟩
        have := Finite.card_le_one_iff_subsingleton.mpr this
        omega
      have hcard : Nat.card {x : V // x ≠ v} = Nat.card V - 1 := card_ne v
      haveI : Nonempty {x : V // x ≠ v} := ⟨⟨u, hu⟩⟩
      have hG' : ¬ HasCompleteMinor (del G v) (s + 1) := fun h =>
        hG (hasCompleteMinor_of_isMinor h (del_isMinor G v))
      have := IHN _ (by omega) {x : V // x ≠ v} rfl _ (del G v) le_rfl inferInstance hG'
      have he := del_edges G v u hu
      rw [hv] at he
      have he' : (G.edgeSet.ncard : ℝ) ≤ (del G v).edgeSet.ncard := by exact_mod_cast (by omega)
      rw [hcard] at this
      have : ((Nat.card V - 1 : ℕ) : ℝ) = (Nat.card V : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      nlinarith
  push Not at hB1
  -- case B2: every edge in many triangles; neighbourhood of a low degree vertex
  have tri : ∀ a b : V, G.Adj a b → d - 1 < ((G.neighborSet a ∩ G.neighborSet b).ncard : ℝ) := by
    intro a b hab
    have hcard : Nat.card {x : V // x ≠ b} = Nat.card V - 1 := card_ne b
    have h1 : 1 ≤ Nat.card V := Nat.card_pos
    have h2 : 2 ≤ Nat.card V := by
      by_contra hc
      have : Nat.card V = 1 := by omega
      have : Subsingleton V := (Finite.card_le_one_iff_subsingleton).mp this.le
      exact hab.ne (Subsingleton.elim a b)
    haveI : Nonempty {x : V // x ≠ b} := ⟨⟨a, hab.ne⟩⟩
    have hG' : ¬ HasCompleteMinor (contr G a b) (s + 1) := fun h =>
      hG (hasCompleteMinor_of_isMinor h (contr_isMinor G hab))
    have := IHN _ (by omega) {x : V // x ≠ b} rfl _ (contr G a b) le_rfl inferInstance hG'
    have he := contr_edges G hab
    rw [hcard] at this
    have hc : ((Nat.card V - 1 : ℕ) : ℝ) = (Nat.card V : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [hc] at this
    have he' : (G.edgeSet.ncard : ℝ) ≤ (contr G a b).edgeSet.ncard + 1 +
        (G.neighborSet a ∩ G.neighborSet b).ncard := by exact_mod_cast (by omega)
    nlinarith
  obtain ⟨v, hv⟩ := exists_deg_le G
  have hv' : (Nat.card V : ℝ) * (G.neighborSet v).ncard ≤ 2 * G.edgeSet.ncard := by
    exact_mod_cast hv
  have hdeg : ((G.neighborSet v).ncard : ℝ) ≤ 2 * d + 2 := by
    by_contra hc
    push Not at hc
    nlinarith
  have hne : (G.neighborSet v).Nonempty := by
    have := hB1 v
    exact (Set.ncard_pos (Set.toFinite _)).mp (by omega)
  haveI : Nonempty (G.neighborSet v) := hne.to_subtype
  have hK := hD (G.neighborSet v) (G.induce (G.neighborSet v)) inferInstance
    (by rw [Nat.card_coe_set_eq]; exact hdeg)
    (fun w => by
      rw [induce_nbr_deg]
      exact tri w.1 v (G.adj_symm w.2))
  exact hG (cone_minor G v s hK)

end extremal
section assembly
variable {V : Type*}

theorem sum_ncard_deg [Fintype V] (G : SimpleGraph V) :
    ∑ v, (G.neighborSet v).ncard = 2 * G.edgeSet.ncard := by
  classical
  have hdeg : ∀ w, (G.neighborSet w).ncard = G.degree w := fun w => by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, card_neighborSet_eq_degree]
  have hE : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']; rfl
  simp only [hdeg, hE]
  convert G.sum_degrees_eq_twice_card_edges

theorem dense_of_extremal (s : ℕ) (f : ℝ) (hf : 0 ≤ f)
    (hE : ∀ (V : Type) [Finite V] (G : SimpleGraph V), Nonempty V → ¬ HasCompleteMinor G s →
      (G.edgeSet.ncard : ℝ) < f * Nat.card V) : Dense s (2 * f + 1) := by
  intro W _ H hW _ hdeg
  by_contra hK
  have h1 := hE W H hW hK
  classical
  letI := Fintype.ofFinite W
  have hs := sum_ncard_deg H
  have hs' : (∑ w, ((H.neighborSet w).ncard : ℝ)) = 2 * H.edgeSet.ncard := by exact_mod_cast hs
  have h2 : (∑ _w : W, (2 * f)) < ∑ w, ((H.neighborSet w).ncard : ℝ) :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun w _ => by linarith [hdeg w])
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card] at h2
  nlinarith

theorem hasCompleteMinor_zero (G : SimpleGraph V) : HasCompleteMinor G 0 :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩

theorem mader_exists (s : ℕ) : ∃ f : ℝ, 0 ≤ f ∧
    ∀ (V : Type) [Finite V] (G : SimpleGraph V), Nonempty V → ¬ HasCompleteMinor G s →
      (G.edgeSet.ncard : ℝ) < f * Nat.card V := by
  induction s with
  | zero => exact ⟨0, le_rfl, fun V _ G _ h => absurd (hasCompleteMinor_zero G) h⟩
  | succ s ih =>
    obtain ⟨f, hf, hE⟩ := ih
    exact ⟨2 * f + 1, by linarith, extremal s (2 * f + 1) (by linarith)
      (dense_of_extremal s f hf hE)⟩

theorem induce_minor (G : SimpleGraph V) (S : Set V) {t : ℕ}
    (h : HasCompleteMinor (G.induce S) t) : HasCompleteMinor G t :=
  hasCompleteMinor_of_isMinor h (isMinor_of_hom (Embedding.induce S).toHom Subtype.val_injective)

theorem induce_deg (G : SimpleGraph V) (S : Set V) (w : S) :
    ((G.induce S).neighborSet w).ncard = (G.neighborSet w.1 ∩ S).ncard := by
  have h : Subtype.val '' ((G.induce S).neighborSet w) = G.neighborSet w.1 ∩ S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← h, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem degenerate_of_extremal {V : Type} [Finite V] (G : SimpleGraph V) (t : ℕ) (d : ℝ)
    (hE : ∀ (V : Type) [Finite V] (G : SimpleGraph V), Nonempty V → ¬ HasCompleteMinor G t →
      (G.edgeSet.ncard : ℝ) < d * Nat.card V)
    (hG : ¬ HasCompleteMinor G t) : IsDegenerate G ⌊2 * d⌋₊ := by
  intro S hS
  haveI : Nonempty S := hS.to_subtype
  have h1 := hE S (G.induce S) inferInstance (fun h => hG (induce_minor G S h))
  obtain ⟨v, hv⟩ := exists_deg_le (G.induce S)
  refine ⟨v.1, v.2, ?_⟩
  rw [← induce_deg]
  apply Nat.le_floor
  have hv' : (Nat.card S : ℝ) * ((G.induce S).neighborSet v).ncard ≤
      2 * (G.induce S).edgeSet.ncard := by exact_mod_cast hv
  have hpos : (0 : ℝ) < Nat.card S := by exact_mod_cast Nat.card_pos
  by_contra hc
  push Not at hc
  nlinarith

theorem colorable_of_degenerate {V : Type} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : IsDegenerate G k) : G.Colorable (k + 1) := by
  classical
  have key : ∀ n, ∀ S : Finset V, S.card = n → ∃ c : V → Fin (k + 1),
      ∀ x ∈ S, ∀ y ∈ S, G.Adj x y → c x ≠ c y := by
    intro n
    induction n with
    | zero =>
      intro S hS
      rw [Finset.card_eq_zero] at hS
      exact ⟨fun _ => 0, by simp [hS]⟩
    | succ n ih =>
      intro S hS
      have hne : (S : Set V).Nonempty := by
        rw [Finset.coe_nonempty, ← Finset.card_pos]; omega
      obtain ⟨v, hvS, hv⟩ := hG (S : Set V) hne
      obtain ⟨c, hc⟩ := ih (S.erase v) (by rw [Finset.card_erase_of_mem hvS]; omega)
      have himg : (c '' (G.neighborSet v ∩ S)).ncard < Fintype.card (Fin (k + 1)) := by
        rw [Fintype.card_fin]
        exact lt_of_le_of_lt (Set.ncard_image_le) (by omega)
      obtain ⟨col, hcol⟩ : ∃ col : Fin (k + 1), col ∉ c '' (G.neighborSet v ∩ S) := by
        by_contra hc'
        push Not at hc'
        have : c '' (G.neighborSet v ∩ S) = Set.univ := Set.eq_univ_of_forall hc'
        rw [this, Set.ncard_univ, Nat.card_eq_fintype_card] at himg
        exact lt_irrefl _ himg
      refine ⟨Function.update c v col, fun x hx y hy hxy => ?_⟩
      by_cases hxv : x = v
      · subst hxv
        have hyv : y ≠ x := (G.ne_of_adj hxy).symm
        rw [Function.update_self, Function.update_of_ne hyv]
        intro h
        exact hcol ⟨y, ⟨hxy, hy⟩, h.symm⟩
      · by_cases hyv : y = v
        · subst hyv
          rw [Function.update_self, Function.update_of_ne hxv]
          intro h
          exact hcol ⟨x, ⟨G.adj_symm hxy, hx⟩, h⟩
        · rw [Function.update_of_ne hxv, Function.update_of_ne hyv]
          exact hc x (Finset.mem_erase.mpr ⟨hxv, hx⟩) y (Finset.mem_erase.mpr ⟨hyv, hy⟩) hxy
  letI := Fintype.ofFinite V
  obtain ⟨c, hc⟩ := key _ Finset.univ rfl
  exact ⟨Coloring.mk c (fun {x y} h => hc x (Finset.mem_univ _) y (Finset.mem_univ _) h)⟩

end assembly

section diam
variable {V W : Type*}

theorem dist_getVert_le (G : SimpleGraph V) (hc : G.Connected) :
    ∀ {u v : V} (p : G.Walk u v) (i : ℕ), i ≤ p.length →
      G.dist u (p.getVert i) ≤ i ∧ G.dist (p.getVert i) v ≤ p.length - i := by
  intro u v p
  induction p with
  | nil =>
    intro i hi
    simp at hi
    subst hi
    simp
  | @cons x y z h q ih =>
    intro i hi
    rcases i with _ | j
    · simp only [Walk.getVert_zero, SimpleGraph.dist_self, le_refl, true_and, Nat.sub_zero]
      exact dist_le _
    · rw [Walk.getVert_cons_succ]
      rw [Walk.length_cons] at hi
      obtain ⟨h1, h2⟩ := ih j (by omega)
      refine ⟨?_, ?_⟩
      · have := hc.dist_triangle (u := x) (v := y) (w := q.getVert j)
        have h3 : G.dist x y = 1 := dist_eq_one_iff_adj.mpr h
        omega
      · rw [Walk.length_cons]; omega

theorem dist_getVert_eq (G : SimpleGraph V) (hc : G.Connected) {u v : V} (p : G.Walk u v)
    (hp : p.length = G.dist u v) (i : ℕ) (hi : i ≤ p.length) : G.dist u (p.getVert i) = i := by
  obtain ⟨h1, h2⟩ := dist_getVert_le G hc p i hi
  have := hc.dist_triangle (u := u) (v := p.getVert i) (w := v)
  omega

theorem dist_le_one_of_mem (G : SimpleGraph V) {x y : V} (h : x = y ∨ G.Adj y x) :
    G.dist y x ≤ 1 := by
  rcases h with rfl | h
  · simp
  · exact (dist_eq_one_iff_adj.mpr h).le

/-- D2: in a connected graph with minimum degree `δ` on `n` vertices, any two vertices are
joined by a walk with `(length + 1) (δ + 1) ≤ 3 n`. -/
theorem short_walk [Finite V] (G : SimpleGraph V) (hc : G.Connected) (δ : ℕ)
    (hδ : ∀ v, δ ≤ (G.neighborSet v).ncard) (a b : V) :
    ∃ p : G.Walk a b, (p.length + 1) * (δ + 1) ≤ 3 * Nat.card V := by
  classical
  haveI := Fintype.ofFinite V
  obtain ⟨p, hp⟩ := hc.exists_walk_length_eq_dist a b
  refine ⟨p, ?_⟩
  set ℓ := p.length with hℓ
  set m := ℓ / 3 with hm
  let q : ℕ → V := fun k => p.getVert (3 * k)
  have hq : ∀ k, k ∈ Finset.range (m + 1) → G.dist a (q k) = 3 * k := by
    intro k hk
    rw [Finset.mem_range] at hk
    exact dist_getVert_eq G hc p hp (3 * k) (by omega)
  let N : ℕ → Finset V := fun k => insert (q k) ((G.neighborSet (q k)).toFinset)
  have hNcard : ∀ k, δ + 1 ≤ (N k).card := by
    intro k
    have hnot : q k ∉ (G.neighborSet (q k)).toFinset := by simp
    rw [Finset.card_insert_of_notMem hnot, ← Set.ncard_eq_toFinset_card']
    have := hδ (q k)
    omega
  have hdisj : ∀ k ∈ Finset.range (m + 1), ∀ k' ∈ Finset.range (m + 1), k ≠ k' →
      Disjoint (N k) (N k') := by
    intro k hk k' hk' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    have e1 : x = q k ∨ G.Adj (q k) x := by
      simpa [N] using hx
    have e2 : x = q k' ∨ G.Adj (q k') x := by
      simpa [N] using hx'
    have d1 := dist_le_one_of_mem G e1
    have d2 := dist_le_one_of_mem G e2
    have d1' : G.dist x (q k) ≤ 1 := by rw [dist_comm]; exact d1
    have d2' : G.dist x (q k') ≤ 1 := by rw [dist_comm]; exact d2
    have t1 := hc.dist_triangle (u := a) (v := q k) (w := x)
    have t2 := hc.dist_triangle (u := a) (v := x) (w := q k')
    have t3 := hc.dist_triangle (u := a) (v := q k') (w := x)
    have t4 := hc.dist_triangle (u := a) (v := x) (w := q k)
    have := hq k hk
    have := hq k' hk'
    omega
  have hsum : ∑ k ∈ Finset.range (m + 1), (N k).card ≤ Fintype.card V := by
    rw [← Finset.card_biUnion hdisj]
    exact Finset.card_le_univ _
  have hlow : (m + 1) * (δ + 1) ≤ ∑ k ∈ Finset.range (m + 1), (N k).card := by
    have := Finset.card_nsmul_le_sum (Finset.range (m + 1)) (fun k => (N k).card) (δ + 1)
      (fun k _ => hNcard k)
    simpa using this
  rw [Nat.card_eq_fintype_card]
  have hl3 : ℓ + 1 ≤ 3 * (m + 1) := by omega
  calc (ℓ + 1) * (δ + 1) ≤ 3 * (m + 1) * (δ + 1) := Nat.mul_le_mul_right _ hl3
    _ = 3 * ((m + 1) * (δ + 1)) := by ring
    _ ≤ 3 * Fintype.card V := by omega

/-- D2 transferred to an induced subgraph: a connected set `P ⊆ S` containing `a, b`. -/
theorem short_set [Finite W] (H : SimpleGraph W) (S : Set W) (hc : (H.induce S).Connected)
    (δ : ℕ) (hδ : ∀ v : S, δ ≤ ((H.induce S).neighborSet v).ncard) (a b : W) (ha : a ∈ S)
    (hb : b ∈ S) :
    ∃ P : Set W, P ⊆ S ∧ a ∈ P ∧ b ∈ P ∧ (H.induce P).Connected ∧
      P.ncard * (δ + 1) ≤ 3 * S.ncard := by
  classical
  obtain ⟨p, hp⟩ := short_walk (H.induce S) hc δ hδ ⟨a, ha⟩ ⟨b, hb⟩
  let f : H.induce S →g H := (Embedding.induce S).toHom
  refine ⟨{v | v ∈ (p.map f).support}, ?_, ?_, ?_, (p.map f).connected_induce_support, ?_⟩
  · intro v hv
    rw [Set.mem_setOf_eq, Walk.support_map, List.mem_map] at hv
    obtain ⟨x, _, rfl⟩ := hv
    exact x.2
  · exact (p.map f).start_mem_support
  · exact (p.map f).end_mem_support
  · have h1 : ({v | v ∈ (p.map f).support} : Set W).ncard ≤ (p.map f).support.length := by
      have : ({v | v ∈ (p.map f).support} : Set W) = ((p.map f).support.toFinset : Set W) := by
        ext v; simp
      rw [this, Set.ncard_coe_finset]
      exact List.toFinset_card_le _
    have h2 : (p.map f).support.length = p.length + 1 := by
      rw [Walk.length_support, Walk.length_map]
    rw [← Nat.card_coe_set_eq S]
    calc _ ≤ (p.length + 1) * (δ + 1) := Nat.mul_le_mul_right _ (h2 ▸ h1)
      _ ≤ _ := hp

end diam



section count
variable {X : Type*}

theorem card_filter_forall [Fintype X] [DecidableEq X] (S : ℕ) (T : Finset X) :
    (Finset.univ.filter fun g : Fin S → X => ∀ k, g k ∈ T).card = T.card ^ S := by
  classical
  have : (Finset.univ.filter fun g : Fin S → X => ∀ k, g k ∈ T) =
      Fintype.piFinset fun _ : Fin S => T := by
    ext g; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- D3: counting choice of `S` sample vertices. -/
theorem sample_exists [Fintype X] [DecidableEq X] (adj : X → X → Prop) [DecidableRel adj]
    (S m : ℕ) (c a : ℝ) (hc0 : 0 ≤ c) (ha : 0 < a)
    (hc : ∀ v, ((Finset.univ.filter fun u => ¬ adj u v).card : ℝ) ≤ c * Fintype.card X)
    (h1 : 2 * Fintype.card X * c ^ S ≤ a)
    (A : Fin m → Finset X) (hA : ∀ j, ((A j).card : ℝ) ≤ a)
    (h2 : m * a ^ S < (Fintype.card X : ℝ) ^ S / 2) :
    ∃ g : Fin S → X, ((Finset.univ.filter fun v => ∀ k, ¬ adj (g k) v).card : ℝ) ≤ a ∧
      ∀ j, ∃ k, g k ∉ A j := by
  classical
  set N := Fintype.card X with hN
  let D : (Fin S → X) → ℕ := fun g => (Finset.univ.filter fun v => ∀ k, ¬ adj (g k) v).card
  have hv : ∀ v, (Finset.univ.filter fun g : Fin S → X => ∀ k, ¬ adj (g k) v).card =
      (Finset.univ.filter fun u => ¬ adj u v).card ^ S := fun v => by
    rw [← card_filter_forall S]
    congr 1
    ext g; simp
  have hswap : ∑ g, D g = ∑ v, (Finset.univ.filter fun u => ¬ adj u v).card ^ S := by
    calc ∑ g, D g = ∑ g : Fin S → X, ∑ v, if (∀ k, ¬ adj (g k) v) then 1 else 0 := by
          simp only [D, Finset.card_filter]
      _ = ∑ v, ∑ g : Fin S → X, if (∀ k, ¬ adj (g k) v) then 1 else 0 := Finset.sum_comm
      _ = ∑ v, (Finset.univ.filter fun g : Fin S → X => ∀ k, ¬ adj (g k) v).card := by
          simp only [Finset.card_filter]
      _ = _ := Finset.sum_congr rfl fun v _ => hv v
  have hsum : (∑ g, (D g : ℝ)) ≤ N * (c * N) ^ S := by
    have : (∑ g, (D g : ℝ)) = ∑ v, ((Finset.univ.filter fun u => ¬ adj u v).card : ℝ) ^ S := by
      exact_mod_cast hswap
    rw [this]
    calc _ ≤ ∑ _v : X, (c * N) ^ S :=
          Finset.sum_le_sum fun v _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (hc v) S
      _ = N * (c * N) ^ S := by simp [hN]
  set Bad1 := Finset.univ.filter fun g : Fin S → X => a < D g with hB1
  have hB1card : (Bad1.card : ℝ) ≤ (N : ℝ) ^ S / 2 := by
    have hm : (Bad1.card : ℝ) * a ≤ ∑ g ∈ Bad1, (D g : ℝ) := by
      have := Finset.card_nsmul_le_sum Bad1 (fun g => (D g : ℝ)) a
        (fun g hg => by
          rw [hB1, Finset.mem_filter] at hg
          exact hg.2.le)
      simpa [nsmul_eq_mul] using this
    have hm2 : ∑ g ∈ Bad1, (D g : ℝ) ≤ ∑ g, (D g : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    have hNS : (N : ℝ) * (c * N) ^ S = (N * c ^ S) * (N : ℝ) ^ S := by ring
    have hpow : 0 ≤ (N : ℝ) ^ S := by positivity
    have : (Bad1.card : ℝ) * a ≤ (a / 2) * (N : ℝ) ^ S := by
      calc _ ≤ (N * c ^ S) * (N : ℝ) ^ S := by linarith
        _ ≤ (a / 2) * (N : ℝ) ^ S := by
          apply mul_le_mul_of_nonneg_right _ hpow
          linarith
    have h' : (Bad1.card : ℝ) * a ≤ ((N : ℝ) ^ S / 2) * a := by nlinarith
    exact le_of_mul_le_mul_right h' ha
  let Bad2 : Fin m → Finset (Fin S → X) := fun j =>
    Finset.univ.filter fun g : Fin S → X => ∀ k, g k ∈ A j
  have hB2 : ∀ j, ((Bad2 j).card : ℝ) ≤ a ^ S := by
    intro j
    simp only [Bad2]
    rw [card_filter_forall S]
    push_cast
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hA j) S
  set U := Bad1 ∪ Finset.univ.biUnion Bad2 with hU
  have hUcard : (U.card : ℝ) < (Finset.univ : Finset (Fin S → X)).card := by
    have e1 : U.card ≤ Bad1.card + ∑ j, (Bad2 j).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    have e2 : ((∑ j, (Bad2 j).card : ℕ) : ℝ) ≤ m * a ^ S := by
      push_cast
      calc _ ≤ ∑ _j : Fin m, a ^ S := Finset.sum_le_sum fun j _ => hB2 j
        _ = m * a ^ S := by simp
    have e3 : ((Finset.univ : Finset (Fin S → X)).card : ℝ) = (N : ℝ) ^ S := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]; push_cast; rfl
    have e1' : (U.card : ℝ) ≤ Bad1.card + ((∑ j, (Bad2 j).card : ℕ) : ℝ) := by
      exact_mod_cast e1
    rw [e3]; linarith
  obtain ⟨g, -, hg⟩ := Finset.exists_mem_notMem_of_card_lt_card (by exact_mod_cast hUcard)
  refine ⟨g, ?_, ?_⟩
  · have : g ∉ Bad1 := fun h => hg (Finset.mem_union_left _ h)
    rw [hB1, Finset.mem_filter] at this
    push_neg at this
    exact this (Finset.mem_univ _)
  · intro j
    have : g ∉ Bad2 j := fun h => hg (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩))
    simp only [Bad2, Finset.mem_filter, Finset.mem_univ, true_and] at this
    push_neg at this
    exact this

end count


open SimpleGraph

section core
variable {W : Type*}

/-- the core conclusion for a set `W1`. -/
def CoreProp (H : SimpleGraph W) (d : ℝ) (W1 : Set W) : Prop :=
  (∀ w ∈ W1, 2 * d / 3 - 2 ≤ ((H.neighborSet w ∩ W1).ncard : ℝ)) ∧
    ∀ U : Set W, (U.ncard : ℝ) ≤ d / 4 → (H.induce (W1 \ U)).Connected

theorem core_of_side [Finite W] (H : SimpleGraph W) (d : ℝ) (hd : 100 ≤ d)
    (hdeg : ∀ w, d - 1 < ((H.neighborSet w).ncard : ℝ))
    (P U0 : Set W) (hN : ∀ v ∈ P, H.neighborSet v ⊆ P ∪ U0) (hP : (P.ncard : ℝ) ≤ d + 1)
    (hU0 : (U0.ncard : ℝ) ≤ d / 3) (hPne : P.Nonempty) : CoreProp H d P := by
  have hdegP : ∀ v ∈ P, 2 * d / 3 - 1 < ((H.neighborSet v ∩ P).ncard : ℝ) := by
    intro v hv
    have h1 : H.neighborSet v \ U0 ⊆ H.neighborSet v ∩ P := by
      intro u hu
      refine ⟨hu.1, ?_⟩
      rcases hN v hv hu.1 with h | h
      · exact h
      · exact absurd h hu.2
    have h2 := Set.ncard_le_ncard h1
    have h3 := Set.le_ncard_sdiff U0 (H.neighborSet v)
    have h4 : ((H.neighborSet v).ncard : ℝ) - U0.ncard ≤ ((H.neighborSet v \ U0).ncard : ℝ) := by
      have : (H.neighborSet v).ncard ≤ (H.neighborSet v \ U0).ncard + U0.ncard := by omega
      have : ((H.neighborSet v).ncard : ℝ) ≤ (H.neighborSet v \ U0).ncard + U0.ncard := by
        exact_mod_cast this
      linarith
    have h5 : ((H.neighborSet v \ U0).ncard : ℝ) ≤ ((H.neighborSet v ∩ P).ncard : ℝ) := by
      exact_mod_cast h2
    linarith [hdeg v]
  refine ⟨fun w hw => by linarith [hdegP w hw], fun U hU => ?_⟩
  rw [connected_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨x, hx⟩ ⟨y, hy⟩
    by_cases hxy : x = y
    · subst hxy; exact Reachable.refl _
    -- a common neighbour in P \ U
    have hxP := hx.1
    have hyP := hy.1
    have hi := Set.ncard_inter_add_ncard_union (H.neighborSet x ∩ P) (H.neighborSet y ∩ P)
    have hu : (H.neighborSet x ∩ P) ∪ (H.neighborSet y ∩ P) ⊆ P :=
      Set.union_subset Set.inter_subset_right Set.inter_subset_right
    have hu2 := Set.ncard_le_ncard hu
    set I := (H.neighborSet x ∩ P) ∩ (H.neighborSet y ∩ P) with hI
    have hIr : (d / 3 - 3 : ℝ) < I.ncard := by
      have e1 := hdegP x hxP
      have e2 := hdegP y hyP
      have : ((I.ncard + ((H.neighborSet x ∩ P) ∪ (H.neighborSet y ∩ P)).ncard : ℕ) : ℝ) =
          ((H.neighborSet x ∩ P).ncard + (H.neighborSet y ∩ P).ncard : ℕ) := by
        exact_mod_cast hi
      push_cast at this
      have e3 : (((H.neighborSet x ∩ P) ∪ (H.neighborSet y ∩ P)).ncard : ℝ) ≤ P.ncard := by
        exact_mod_cast hu2
      linarith
    have hID : (0 : ℝ) < (I \ U).ncard := by
      have h3 := Set.le_ncard_sdiff U I
      have : I.ncard ≤ (I \ U).ncard + U.ncard := by omega
      have : (I.ncard : ℝ) ≤ (I \ U).ncard + U.ncard := by exact_mod_cast this
      linarith
    have hne : (I \ U).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      rw [h, Set.ncard_empty] at hID
      simp at hID
    obtain ⟨z, hzI, hzU⟩ := hne
    have hz : z ∈ P \ U := ⟨hzI.1.2, hzU⟩
    have a1 : H.Adj x z := hzI.1.1
    have a2 : H.Adj z y := (hzI.2.1 : H.Adj y z).symm
    have r1 : (H.induce (P \ U)).Reachable ⟨x, hx⟩ ⟨z, hz⟩ :=
      SimpleGraph.Adj.reachable (show H.Adj x z from a1)
    have r2 : (H.induce (P \ U)).Reachable ⟨z, hz⟩ ⟨y, hy⟩ :=
      SimpleGraph.Adj.reachable (show H.Adj z y from a2)
    exact r1.trans r2
  · -- nonempty
    obtain ⟨v, hv⟩ := hPne
    have e1 := hdegP v hv
    have e2 := Set.ncard_le_ncard (Set.inter_subset_right : H.neighborSet v ∩ P ⊆ P)
    have e2' : ((H.neighborSet v ∩ P).ncard : ℝ) ≤ P.ncard := by exact_mod_cast e2
    have h3 := Set.le_ncard_sdiff U P
    have : P.ncard ≤ (P \ U).ncard + U.ncard := by omega
    have : (P.ncard : ℝ) ≤ (P \ U).ncard + U.ncard := by exact_mod_cast this
    have hpos : (0 : ℝ) < (P \ U).ncard := by linarith
    have hne : (P \ U).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      rw [h, Set.ncard_empty] at hpos
      simp at hpos
    obtain ⟨w, hw⟩ := hne
    exact ⟨⟨w, hw⟩⟩

/-- D1: a highly connected core of a dense graph on at most `2d+2` vertices. -/
theorem dense_core [Finite W] (H : SimpleGraph W) (d : ℝ) (hd : 100 ≤ d)
    (hcard : (Nat.card W : ℝ) ≤ 2 * d + 2)
    (hdeg : ∀ w, d - 1 < ((H.neighborSet w).ncard : ℝ)) (hne : Nonempty W) :
    ∃ W1 : Set W, W1.Nonempty ∧ CoreProp H d W1 := by
  by_cases hall : ∀ U : Set W, (U.ncard : ℝ) ≤ d / 3 → (H.induce Uᶜ).Connected
  · refine ⟨Set.univ, Set.univ_nonempty, fun w _ => ?_, fun U hU => ?_⟩
    · rw [Set.inter_univ]; linarith [hdeg w]
    · rw [← Set.compl_eq_univ_sdiff]
      exact hall U (by linarith)
  push_neg at hall
  obtain ⟨U0, hU0, hnc⟩ := hall
  -- U0ᶜ is nonempty
  obtain ⟨w0⟩ := hne
  have hcW : d - 1 < (Nat.card W : ℝ) := by
    have := Set.ncard_le_ncard (Set.subset_univ (H.neighborSet w0))
    rw [Set.ncard_univ] at this
    have : ((H.neighborSet w0).ncard : ℝ) ≤ Nat.card W := by exact_mod_cast this
    linarith [hdeg w0]
  have hcompl : (U0ᶜ).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    rw [h, Set.ncard_univ] at hU0
    linarith
  have hnp : ¬ (H.induce U0ᶜ).Preconnected := by
    intro hp
    obtain ⟨v, hv⟩ := hcompl
    exact hnc ((connected_iff _).mpr ⟨hp, ⟨⟨v, hv⟩⟩⟩)
  rw [Preconnected] at hnp
  push_neg at hnp
  obtain ⟨x, y, hxy⟩ := hnp
  set A : Set W := {v | ∃ h : v ∉ U0, (H.induce U0ᶜ).Reachable x ⟨v, h⟩} with hA
  set B : Set W := U0ᶜ \ A with hB
  have hclos : ∀ v ∈ A, ∀ u, u ∉ U0 → H.Adj v u → u ∈ A := by
    rintro v ⟨hv, r⟩ u hu h
    exact ⟨hu, r.trans (SimpleGraph.Adj.reachable (show H.Adj v u from h))⟩
  have hNA : ∀ v ∈ A, H.neighborSet v ⊆ A ∪ U0 := by
    intro v hv u hu
    by_cases hu0 : u ∈ U0
    · exact Or.inr hu0
    · exact Or.inl (hclos v hv u hu0 hu)
  have hNB : ∀ v ∈ B, H.neighborSet v ⊆ B ∪ U0 := by
    intro v hv u hu
    by_cases hu0 : u ∈ U0
    · exact Or.inr hu0
    · left
      refine ⟨hu0, fun huA => hv.2 (hclos u huA v hv.1 (H.adj_symm hu))⟩
  have hxA : x.1 ∈ A := ⟨x.2, Reachable.refl _⟩
  have hyB : y.1 ∈ B := ⟨y.2, fun ⟨h, r⟩ => hxy r⟩
  have hdisj : Disjoint A B := Set.disjoint_sdiff_right
  have hsum : (A.ncard : ℝ) + B.ncard ≤ 2 * d + 2 := by
    have := Set.ncard_union_eq hdisj
    have h2 := Set.ncard_le_ncard (Set.subset_univ (A ∪ B))
    rw [Set.ncard_univ] at h2
    have : ((A.ncard + B.ncard : ℕ) : ℝ) ≤ Nat.card W := by exact_mod_cast (this ▸ h2)
    push_cast at this
    linarith
  rcases le_total (A.ncard : ℝ) B.ncard with h | h
  · exact ⟨A, ⟨_, hxA⟩, core_of_side H d hd hdeg A U0 hNA (by linarith) hU0 ⟨_, hxA⟩⟩
  · exact ⟨B, ⟨_, hyB⟩, core_of_side H d hd hdeg B U0 hNB (by linarith) hU0 ⟨_, hyB⟩⟩

end core

section iter
variable {W : Type*}

theorem reach_sub_i (G : SimpleGraph W) {s t : Set W} (hst : s ⊆ t) {a b : W} (ha : a ∈ s)
    (hb : b ∈ s) (h : (G.induce s).Reachable ⟨a, ha⟩ ⟨b, hb⟩) :
    (G.induce t).Reachable ⟨a, hst ha⟩ ⟨b, hst hb⟩ :=
  h.map (induceHomOfLE G hst).toHom

theorem induce_deg_i (G : SimpleGraph W) (S : Set W) (w : S) :
    ((G.induce S).neighborSet w).ncard = (G.neighborSet w.1 ∩ S).ncard := by
  have h : Subtype.val '' ((G.induce S).neighborSet w) = G.neighborSet w.1 ∩ S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨x, h2⟩, h1, rfl⟩
  rw [← h, Set.ncard_image_of_injective _ Subtype.val_injective]

theorem card_filter_sub (T : Set W) [Fintype T] (q : W → Prop) [DecidablePred q] :
    ((Finset.univ : Finset T).filter (fun x => q x.1)).card = {v | v ∈ T ∧ q v}.ncard := by
  classical
  calc _ = ((((Finset.univ : Finset T).filter (fun x => q x.1)) : Set T)).ncard :=
        (Set.ncard_coe_finset _).symm
    _ = (Subtype.val '' ((((Finset.univ : Finset T).filter (fun x => q x.1)) : Set T))).ncard :=
        (Set.ncard_image_of_injective _ Subtype.val_injective).symm
    _ = _ := by
        congr 1
        ext v
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_image, Set.mem_setOf_eq,
          Subtype.exists, exists_and_right, exists_eq_right]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩

theorem union_conn (H : SimpleGraph W) (S : ℕ) (hS : 0 < S) (P : Fin S → Set W) (x : W)
    (hx : ∀ k, x ∈ P k) (hP : ∀ k, (H.induce (P k)).Connected) :
    (H.induce (⋃ k, P k)).Connected := by
  have hxU : x ∈ ⋃ k, P k := Set.mem_iUnion.2 ⟨⟨0, hS⟩, hx _⟩
  have key : ∀ v (hv : v ∈ ⋃ k, P k), (H.induce (⋃ k, P k)).Reachable ⟨v, hv⟩ ⟨x, hxU⟩ := by
    intro v hv
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hv
    exact reach_sub_i H (Set.subset_iUnion P k) hk (hx k)
      ((hP k).preconnected ⟨v, hk⟩ ⟨x, hx k⟩)
  rw [connected_iff]
  refine ⟨?_, ⟨⟨x, hxU⟩⟩⟩
  rintro ⟨u, hu⟩ ⟨v, hv⟩
  exact (key u hu).trans (key v hv).symm

/-- the iteration invariant. -/
def KTInv (H : SimpleGraph W) (W1 : Set W) (S : ℕ) (a : ℝ) (i : ℕ) (B : ℕ → Set W) : Prop :=
  ∀ j < i, B j ⊆ W1 ∧ (H.induce (B j)).Connected ∧ (B j).ncard ≤ 15 * S ∧
    (∀ j' < j, Disjoint (B j') (B j) ∧ ∃ u ∈ B j', ∃ v ∈ B j, H.Adj u v) ∧
    ({v | v ∈ W1 ∧ v ∉ (⋃ k ∈ Finset.range (j + 1), B k) ∧ ∀ u ∈ B j, ¬ H.Adj u v}.ncard : ℝ) ≤ a

theorem iUnion_range_congr (B B' : ℕ → Set W) (n : ℕ) (h : ∀ k < n, B' k = B k) :
    (⋃ k ∈ Finset.range n, B' k) = ⋃ k ∈ Finset.range n, B k := by
  ext v
  simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
  constructor
  · rintro ⟨k, hk, hv⟩; exact ⟨k, hk, h k hk ▸ hv⟩
  · rintro ⟨k, hk, hv⟩; exact ⟨k, hk, (h k hk).symm ▸ hv⟩

theorem inv_step [Finite W] (H : SimpleGraph W) (d : ℝ) (hd : 100 ≤ d)
    (hcard : (Nat.card W : ℝ) ≤ 2 * d + 2) (W1 : Set W) (hW1 : CoreProp H d W1) (S s : ℕ)
    (hS : 0 < S) (a : ℝ) (ha : 0 < a) (h1 : 2 * (2 * d + 2) * (6 / 7 : ℝ) ^ S ≤ a)
    (h2 : (s : ℝ) * a ^ S < (d / 3) ^ S / 2) (h3 : (s : ℝ) * (15 * S) ≤ d / 4)
    (i : ℕ) (hi : i < s) (B : ℕ → Set W) (hB : KTInv H W1 S a i B) :
    ∃ B' : ℕ → Set W, KTInv H W1 S a (i + 1) B' := by
  classical
  set U := ⋃ k ∈ Finset.range i, B k with hU
  have hUc : (U.ncard : ℝ) ≤ d / 4 := by
    have e1 := Finset.set_ncard_biUnion_le (Finset.range i) B
    have e2 : ∑ k ∈ Finset.range i, (B k).ncard ≤ ∑ _k ∈ Finset.range i, 15 * S :=
      Finset.sum_le_sum fun k hk => (hB k (Finset.mem_range.1 hk)).2.2.1
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at e2
    have : (U.ncard : ℝ) ≤ (i * (15 * S) : ℕ) := by exact_mod_cast e1.trans e2
    push_cast at this
    have : (i : ℝ) * (15 * S) ≤ s * (15 * S) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) (by positivity)
    linarith
  set W' := W1 \ U with hW'
  have hconn := hW1.2 U hUc
  have hdeg : ∀ v : W', 5 * d / 12 - 2 ≤ (((H.induce W').neighborSet v).ncard : ℝ) := by
    intro v
    rw [induce_deg_i]
    have hsub : H.neighborSet v.1 ∩ W1 ⊆ (H.neighborSet v.1 ∩ W') ∪ U := by
      intro u ⟨hu1, hu2⟩
      by_cases huU : u ∈ U
      · exact Or.inr huU
      · exact Or.inl ⟨hu1, hu2, huU⟩
    have e1 := (Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
    have e1' : ((H.neighborSet v.1 ∩ W1).ncard : ℝ) ≤ (H.neighborSet v.1 ∩ W').ncard + U.ncard := by
      exact_mod_cast e1
    have := hW1.1 v.1 v.2.1
    linarith
  set δ := ⌈5 * d / 12 - 2⌉₊ with hδdef
  have hδ : ∀ v : W', δ ≤ ((H.induce W').neighborSet v).ncard := fun v =>
    Nat.ceil_le.mpr (hdeg v)
  have hδr : 5 * d / 12 - 2 ≤ (δ : ℝ) := Nat.le_ceil _
  have hW'le : (W'.ncard : ℝ) ≤ 2 * d + 2 := by
    have := Set.ncard_le_ncard (Set.subset_univ W')
    rw [Set.ncard_univ] at this
    have : (W'.ncard : ℝ) ≤ Nat.card W := by exact_mod_cast this
    linarith
  obtain ⟨⟨v0, hv0⟩⟩ := hconn.nonempty
  have hW'ge : d / 3 ≤ (W'.ncard : ℝ) := by
    have e := hdeg ⟨v0, hv0⟩
    rw [induce_deg_i] at e
    have := Set.ncard_le_ncard (Set.inter_subset_right : H.neighborSet v0 ∩ W' ⊆ W')
    have : ((H.neighborSet v0 ∩ W').ncard : ℝ) ≤ W'.ncard := by exact_mod_cast this
    linarith
  haveI : Fintype W' := Fintype.ofFinite W'
  have hcardX : (Fintype.card W' : ℝ) = W'.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  let A : Fin i → Finset W' := fun j =>
    (Finset.univ : Finset W').filter (fun v => (fun w => ∀ u ∈ B j, ¬ H.Adj u w) v.1)
  have hA : ∀ j, ((A j).card : ℝ) ≤ a := by
    intro j
    simp only [A]
    rw [card_filter_sub W' (fun w => ∀ u ∈ B j, ¬ H.Adj u w)]
    have hsub : {v | v ∈ W' ∧ ∀ u ∈ B j, ¬ H.Adj u v} ⊆
        {v | v ∈ W1 ∧ v ∉ (⋃ k ∈ Finset.range (j.1 + 1), B k) ∧ ∀ u ∈ B j, ¬ H.Adj u v} := by
      rintro v ⟨⟨hv1, hv2⟩, hv3⟩
      refine ⟨hv1, fun hv => hv2 ?_, hv3⟩
      rw [hU]
      simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hv ⊢
      obtain ⟨k, hk, hvk⟩ := hv
      exact ⟨k, by omega, hvk⟩
    have := Set.ncard_le_ncard hsub
    have : (({v | v ∈ W' ∧ ∀ u ∈ B j, ¬ H.Adj u v} : Set W).ncard : ℝ) ≤
        ({v | v ∈ W1 ∧ v ∉ (⋃ k ∈ Finset.range (j.1 + 1), B k) ∧ ∀ u ∈ B j, ¬ H.Adj u v} :
          Set W).ncard := by exact_mod_cast this
    exact this.trans (hB j.1 j.2).2.2.2.2
  have hc : ∀ v : W', (((Finset.univ : Finset W').filter fun u => ¬ H.Adj u.1 v.1).card : ℝ) ≤
      6 / 7 * Fintype.card W' := by
    intro v
    have e := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset W'))
      (fun u : W' => H.Adj u.1 v.1)
    rw [Finset.card_univ] at e
    have e2 : ((Finset.univ : Finset W').filter fun u => H.Adj u.1 v.1).card =
        (H.neighborSet v.1 ∩ W').ncard := by
      rw [card_filter_sub W' (fun w => H.Adj w v.1)]
      congr 1
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, mem_neighborSet]
      exact ⟨fun ⟨h1, h2⟩ => ⟨H.adj_symm h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, H.adj_symm h1⟩⟩
    have e3 := hdeg v
    rw [induce_deg_i] at e3
    have e' : (((Finset.univ : Finset W').filter fun u => ¬ H.Adj u.1 v.1).card : ℝ) =
        Fintype.card W' - (H.neighborSet v.1 ∩ W').ncard := by
      rw [← e2]
      have : ((((Finset.univ : Finset W').filter fun u => H.Adj u.1 v.1).card +
          ((Finset.univ : Finset W').filter fun u => ¬ H.Adj u.1 v.1).card : ℕ) : ℝ) =
          Fintype.card W' := by exact_mod_cast e
      push_cast at this
      linarith
    rw [e', hcardX]
    linarith
  have h1' : 2 * (Fintype.card W' : ℝ) * (6 / 7) ^ S ≤ a := by
    rw [hcardX]
    have : (0 : ℝ) ≤ (6 / 7) ^ S := by positivity
    nlinarith
  have h2' : (i : ℝ) * a ^ S < (Fintype.card W' : ℝ) ^ S / 2 := by
    rw [hcardX]
    have e1 : (i : ℝ) * a ^ S ≤ s * a ^ S :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hi.le) (by positivity)
    have e2 : (d / 3) ^ S ≤ (W'.ncard : ℝ) ^ S := pow_le_pow_left₀ (by linarith) hW'ge S
    linarith
  obtain ⟨g, hg1, hg2⟩ := sample_exists (X := W') (fun u v => H.Adj u.1 v.1) S i (6 / 7) a
    (by norm_num) ha hc h1' A hA h2'
  have hP : ∀ k : Fin S, ∃ P : Set W, P ⊆ W' ∧ (g ⟨0, hS⟩).1 ∈ P ∧ (g k).1 ∈ P ∧
      (H.induce P).Connected ∧ P.ncard * (δ + 1) ≤ 3 * W'.ncard := fun k =>
    short_set H W' hconn δ hδ _ _ (g ⟨0, hS⟩).2 (g k).2
  choose P hPW hP0 hPk hPc hPn using hP
  have hPn' : ∀ k, (P k).ncard ≤ 15 := by
    intro k
    by_contra hk
    push_neg at hk
    have e1 : (16 : ℝ) ≤ (P k).ncard := by exact_mod_cast hk
    have e2 : ((P k).ncard : ℝ) * (δ + 1) ≤ 3 * W'.ncard := by exact_mod_cast hPn k
    nlinarith
  set Bn := ⋃ k, P k with hBn
  have hBnW : Bn ⊆ W' := Set.iUnion_subset hPW
  have hBnc : (H.induce Bn).Connected := union_conn H S hS P _ hP0 hPc
  have hBnn : Bn.ncard ≤ 15 * S := by
    have := Set.ncard_iUnion_le_of_fintype P
    have e2 : ∑ k, (P k).ncard ≤ ∑ _k : Fin S, 15 := Finset.sum_le_sum fun k _ => hPn' k
    calc Bn.ncard ≤ ∑ k, (P k).ncard := this
      _ ≤ ∑ _k : Fin S, 15 := e2
      _ = 15 * S := by simp [mul_comm]
  refine ⟨fun n => if n = i then Bn else B n, fun j hj => ?_⟩
  have hcongr : ∀ n ≤ i, (⋃ k ∈ Finset.range n, (if k = i then Bn else B k)) =
      ⋃ k ∈ Finset.range n, B k := fun n hn =>
    iUnion_range_congr B (fun k => if k = i then Bn else B k) n (fun k hk => if_neg (by omega))
  dsimp only
  rcases Nat.lt_or_ge j i with hji | hji
  · obtain ⟨b1, b2, b3, b4, b5⟩ := hB j hji
    rw [if_neg (show j ≠ i by omega)]
    refine ⟨b1, b2, b3, fun j' hj' => ?_, ?_⟩
    · rw [if_neg (show j' ≠ i by omega)]
      exact b4 j' hj'
    · rw [hcongr (j + 1) (by omega)]
      exact b5
  · have hji' : j = i := by omega
    subst hji'
    rw [if_pos rfl]
    refine ⟨hBnW.trans Set.diff_subset, hBnc, hBnn, fun j' hj' => ?_, ?_⟩
    · rw [if_neg (show j' ≠ j by omega)]
      refine ⟨?_, ?_⟩
      · rw [Set.disjoint_left]
        intro v hv hv'
        have := (hBnW hv').2
        exact this (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_range.2 hj')) hv)
      · obtain ⟨k, hk⟩ := hg2 ⟨j', hj'⟩
        simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hk
        push_neg at hk
        obtain ⟨u, hu, hadj⟩ := hk
        exact ⟨u, hu, (g k).1, Set.mem_iUnion.2 ⟨k, hPk k⟩, hadj⟩
    · have hsub : {v | v ∈ W1 ∧ v ∉ (⋃ k ∈ Finset.range (j + 1),
          (if k = j then Bn else B k)) ∧ ∀ u ∈ Bn, ¬ H.Adj u v} ⊆
          {v | v ∈ W' ∧ ∀ k, ¬ H.Adj (g k).1 v} := by
        rintro v ⟨hv1, hv2, hv3⟩
        refine ⟨⟨hv1, fun hvU => hv2 ?_⟩, fun k => hv3 _ (Set.mem_iUnion.2 ⟨k, hPk k⟩)⟩
        rw [hU] at hvU
        simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hvU ⊢
        obtain ⟨k, hk, hvk⟩ := hvU
        exact ⟨k, by omega, by rw [if_neg (show k ≠ j by omega)]; exact hvk⟩
      have e1 := Set.ncard_le_ncard hsub
      rw [← card_filter_sub W' (fun w => ∀ k, ¬ H.Adj (g k).1 w)] at e1
      have e1' : (({v | v ∈ W1 ∧ v ∉ (⋃ k ∈ Finset.range (j + 1),
          (if k = j then Bn else B k)) ∧ ∀ u ∈ Bn, ¬ H.Adj u v} : Set W).ncard : ℝ) ≤
          ((Finset.univ : Finset W').filter fun x => ∀ k, ¬ H.Adj (g k).1 x.1).card := by
        exact_mod_cast e1
      exact e1'.trans hg1

/-- D4: branch sets of a `K_s` minor inside the core. -/
theorem branch_sets [Finite W] (H : SimpleGraph W) (d : ℝ) (hd : 100 ≤ d)
    (hcard : (Nat.card W : ℝ) ≤ 2 * d + 2) (W1 : Set W) (hW1 : CoreProp H d W1) (S s : ℕ)
    (hS : 0 < S) (a : ℝ) (ha : 0 < a) (h1 : 2 * (2 * d + 2) * (6 / 7 : ℝ) ^ S ≤ a)
    (h2 : (s : ℝ) * a ^ S < (d / 3) ^ S / 2) (h3 : (s : ℝ) * (15 * S) ≤ d / 4) :
    ∃ B : ℕ → Set W, ∀ j < s, (H.induce (B j)).Connected ∧
      ∀ j' < j, Disjoint (B j') (B j) ∧ ∃ u ∈ B j', ∃ v ∈ B j, H.Adj u v := by
  have key : ∀ i ≤ s, ∃ B, KTInv H W1 S a i B := by
    intro i
    induction i with
    | zero => exact fun _ => ⟨fun _ => ∅, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    | succ i ih =>
      intro hi
      obtain ⟨B, hB⟩ := ih (by omega)
      exact inv_step H d hd hcard W1 hW1 S s hS a ha h1 h2 h3 i (by omega) B hB
  obtain ⟨B, hB⟩ := key s le_rfl
  exact ⟨B, fun j hj => ⟨(hB j hj).2.1, (hB j hj).2.2.2.1⟩⟩

end iter

section final

theorem colorable_of_le {V : Type} (G : SimpleGraph V) {n : ℕ} {x : ℝ} (hG : G.Colorable n)
    (h : (n : ℝ) ≤ x) : G.Colorable ⌈x⌉₊ :=
  hG.mono (by exact_mod_cast h.trans (Nat.le_ceil x))

theorem kt_of_denseLarge (hL : ∃ K T0 : ℝ, 0 < K ∧
    ∀ t : ℕ, T0 ≤ t → Dense (t - 1) (K * t * Real.sqrt (Real.log t))) :
    ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      ¬ HasCompleteMinor G t → G.Colorable ⌈C * t * Real.sqrt (Real.log t)⌉₊ := by
  obtain ⟨K, T0, hK, hD⟩ := hL
  choose f hf0 hfE using mader_exists
  set M : ℕ := max ⌈T0⌉₊ 3 with hM
  set Cs : ℝ := ∑ t ∈ Finset.range M, (2 * f t + 1) / (t * Real.sqrt (Real.log t)) with hCs
  refine ⟨max Cs (2 * K + 1), fun t ht V _ G hG => ?_⟩
  have hlog : ∀ t : ℕ, 2 ≤ t → 0 < (t : ℝ) * Real.sqrt (Real.log t) := fun t h2 => by
    have : (2 : ℝ) ≤ t := by exact_mod_cast h2
    have : 0 < Real.log t := Real.log_pos (by linarith)
    positivity
  rcases Nat.lt_or_ge t 2 with h1 | h2
  · -- t = 1 : no vertices
    have ht1 : t = 1 := by omega
    subst ht1
    haveI : IsEmpty V := ⟨fun v => hG ⟨fun _ => {v}, fun _ => induce_singleton_conn G v,
      fun i j hij => absurd (Subsingleton.elim i j) hij, fun i j hij => absurd (Subsingleton.elim i j) hij.ne⟩⟩
    exact ⟨Coloring.ofIsEmpty⟩
  rcases Nat.lt_or_ge t M with hs | hl
  · -- small t
    have hcol := colorable_of_degenerate G _ (degenerate_of_extremal G t (f t) (hfE t) hG)
    apply colorable_of_le G hcol
    have hpos := hlog t h2
    have hterm : (2 * f t + 1) / (t * Real.sqrt (Real.log t)) ≤ Cs := by
      rw [hCs]
      apply Finset.single_le_sum (f := fun t : ℕ => (2 * f t + 1) / (t * Real.sqrt (Real.log t)))
        (fun i _ => by
          have := hf0 i
          positivity) (Finset.mem_range.mpr hs)
    have hC : (2 * f t + 1) / (t * Real.sqrt (Real.log t)) ≤ max Cs (2 * K + 1) :=
      hterm.trans (le_max_left _ _)
    rw [div_le_iff₀ hpos] at hC
    have hfl : ((⌊2 * f t⌋₊ : ℕ) : ℝ) ≤ 2 * f t := Nat.floor_le (by linarith [hf0 t])
    push_cast
    nlinarith
  · -- large t
    have hT0 : T0 ≤ t := (Nat.le_ceil T0).trans (by exact_mod_cast (le_max_left _ _).trans hl)
    have h3 : (3 : ℝ) ≤ t := by exact_mod_cast (le_max_right _ _).trans hl
    have hlog1 : 1 ≤ Real.log t := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      linarith [Real.exp_one_lt_d9]
    have hsq : 1 ≤ Real.sqrt (Real.log t) := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlog1
    set d := K * t * Real.sqrt (Real.log t) with hd
    have hdpos : 0 < d := by positivity
    have hE := extremal (t - 1) d hdpos (hD t hT0)
    rw [Nat.sub_add_cancel ht] at hE
    have hcol := colorable_of_degenerate G _ (degenerate_of_extremal G t d hE hG)
    apply colorable_of_le G hcol
    have hfl : ((⌊2 * d⌋₊ : ℕ) : ℝ) ≤ 2 * d := Nat.floor_le (by linarith)
    have hts : 1 ≤ (t : ℝ) * Real.sqrt (Real.log t) := by nlinarith
    have hmax : 2 * K + 1 ≤ max Cs (2 * K + 1) := le_max_right _ _
    push_cast
    have : (2 * K + 1) * ((t : ℝ) * Real.sqrt (Real.log t)) ≤
        max Cs (2 * K + 1) * ((t : ℝ) * Real.sqrt (Real.log t)) :=
      mul_le_mul_of_nonneg_right hmax (by linarith)
    nlinarith

end final


section asym

theorem minor_of_branch {W : Type*} (H : SimpleGraph W) (s : ℕ) (B : ℕ → Set W)
    (hB : ∀ j < s, (H.induce (B j)).Connected ∧
      ∀ j' < j, Disjoint (B j') (B j) ∧ ∃ u ∈ B j', ∃ v ∈ B j, H.Adj u v) :
    HasCompleteMinor H s := by
  refine ⟨fun i => B i.1, fun i => (hB i.1 i.2).1, fun i j hij => ?_, fun i j hij => ?_⟩
  · have hne : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ((hB j.1 j.2).2 i.1 h).1
    · exact ((hB i.1 i.2).2 j.1 h).1.symm
  · have hne : i.1 ≠ j.1 := fun h => hij.ne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · exact ((hB j.1 j.2).2 i.1 h).2
    · obtain ⟨u, hu, v, hv, huv⟩ := ((hB i.1 i.2).2 j.1 h).2
      exact ⟨v, hv, u, hu, huv.symm⟩

theorem key_ineq (L : ℝ) (hL : 0 ≤ L) (S : ℕ) (hS42 : 42 ≤ S) (hS : 14 * (L + 1) ≤ (S : ℝ) ^ 2) :
    Real.exp L * 18 ^ S * (6 / 7 : ℝ) ^ (S * S) < 1 / 2 := by
  have e18 : (18 : ℝ) ≤ Real.exp 3 := by
    have h1 := Real.exp_one_gt_d9
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h1.le 3
    rw [h3]; norm_num at this; linarith
  have e67 : (6 / 7 : ℝ) ≤ Real.exp (-1 / 7) := by
    have := Real.add_one_le_exp (-1 / 7); linarith
  have p1 : (18 : ℝ) ^ S ≤ Real.exp 3 ^ S := pow_le_pow_left₀ (by norm_num) e18 S
  have p2 : (6 / 7 : ℝ) ^ (S * S) ≤ Real.exp (-1 / 7) ^ (S * S) :=
    pow_le_pow_left₀ (by norm_num) e67 _
  rw [← Real.exp_nat_mul] at p1 p2
  have hprod : Real.exp L * 18 ^ S * (6 / 7 : ℝ) ^ (S * S) ≤
      Real.exp L * Real.exp (S * 3) * Real.exp (((S * S : ℕ) : ℝ) * (-1 / 7)) := by
    have q1 : (0 : ℝ) ≤ (6 / 7 : ℝ) ^ (S * S) := by positivity
    have q2 : (0 : ℝ) ≤ Real.exp L := (Real.exp_pos L).le
    have q3 : Real.exp L * 18 ^ S ≤ Real.exp L * Real.exp (S * 3) :=
      mul_le_mul_of_nonneg_left p1 q2
    calc _ ≤ Real.exp L * Real.exp (S * 3) * (6 / 7 : ℝ) ^ (S * S) :=
          mul_le_mul_of_nonneg_right q3 q1
      _ ≤ _ := mul_le_mul_of_nonneg_left p2 (by positivity)
  rw [← Real.exp_add, ← Real.exp_add] at hprod
  have hexp : L + S * 3 + ((S * S : ℕ) : ℝ) * (-1 / 7) ≤ -1 := by
    push_cast
    have : (42 : ℝ) ≤ S := by exact_mod_cast hS42
    nlinarith
  have hm1 : Real.exp (-1) < 1 / 2 := by
    have h1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
    have := Real.exp_one_gt_d9
    nlinarith [Real.exp_pos (-1)]
  calc _ ≤ _ := hprod
    _ ≤ Real.exp (-1) := Real.exp_le_exp.mpr hexp
    _ < 1 / 2 := hm1

theorem dense_large : ∃ K T0 : ℝ, 0 < K ∧
    ∀ t : ℕ, T0 ≤ t → Dense (t - 1) (K * t * Real.sqrt (Real.log t)) := by
  refine ⟨50000, 3, by norm_num, fun t ht => ?_⟩
  intro W _ H hne hcard hdeg
  have h3 : (3 : ℝ) ≤ t := ht
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : 1 ≤ t := by
    have : (1 : ℝ) ≤ t := by linarith
    exact_mod_cast this
  set L := Real.log t with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le htpos]; linarith [Real.exp_one_lt_d9]
  have hsq : 1 ≤ Real.sqrt L := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hL1
  set d := 50000 * (t : ℝ) * Real.sqrt L with hd
  have htsq : 3 ≤ (t : ℝ) * Real.sqrt L := by nlinarith
  have hd100 : 100 ≤ d := by rw [hd]; nlinarith
  set S : ℕ := ⌈Real.sqrt (14 * (L + 1))⌉₊ + 42 with hS
  have hS42 : 42 ≤ S := by omega
  have hSsq : 14 * (L + 1) ≤ (S : ℝ) ^ 2 := by
    have e1 : Real.sqrt (14 * (L + 1)) ≤ (S : ℝ) := by
      have := Nat.le_ceil (Real.sqrt (14 * (L + 1)))
      rw [hS]; push_cast; linarith
    have e2 := Real.sq_sqrt (show (0 : ℝ) ≤ 14 * (L + 1) by linarith)
    nlinarith [Real.sqrt_nonneg (14 * (L + 1))]
  have hSup : (S : ℝ) ≤ 49 * Real.sqrt L := by
    have e1 : (⌈Real.sqrt (14 * (L + 1))⌉₊ : ℝ) < Real.sqrt (14 * (L + 1)) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    have e2 : Real.sqrt (14 * (L + 1)) ≤ 6 * Real.sqrt L := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      nlinarith
    rw [hS]; push_cast; nlinarith
  set ρ : ℝ := 18 * (6 / 7 : ℝ) ^ S with hρ
  set a : ℝ := d / 3 * ρ with ha
  have hρpos : 0 < ρ := by positivity
  have hdpos : 0 < d := by linarith
  have hapos : 0 < a := by positivity
  have h1 : 2 * (2 * d + 2) * (6 / 7 : ℝ) ^ S ≤ a := by
    have hp : 0 ≤ (6 / 7 : ℝ) ^ S := by positivity
    have : 4 * d + 4 ≤ 6 * d := by linarith
    calc 2 * (2 * d + 2) * (6 / 7 : ℝ) ^ S = (4 * d + 4) * (6 / 7 : ℝ) ^ S := by ring
      _ ≤ (6 * d) * (6 / 7 : ℝ) ^ S := mul_le_mul_of_nonneg_right this hp
      _ = a := by rw [ha, hρ]; ring
  have hs_le : ((t - 1 : ℕ) : ℝ) ≤ t := by
    have : t - 1 ≤ t := Nat.sub_le t 1
    exact_mod_cast this
  have h2 : ((t - 1 : ℕ) : ℝ) * a ^ S < (d / 3) ^ S / 2 := by
    have hk := key_ineq L (by linarith) S hS42 hSsq
    rw [hLdef, Real.exp_log htpos] at hk
    have hρS : ρ ^ S = 18 ^ S * (6 / 7 : ℝ) ^ (S * S) := by rw [hρ, mul_pow, ← pow_mul]
    have haS : a ^ S = (d / 3) ^ S * ρ ^ S := by rw [ha, mul_pow]
    have hd3 : 0 < (d / 3) ^ S := by positivity
    have hρS0 : 0 ≤ ρ ^ S := by positivity
    have hlt : (t : ℝ) * ρ ^ S < 1 / 2 := by rw [hρS, ← mul_assoc]; exact hk
    have hle : ((t - 1 : ℕ) : ℝ) * ρ ^ S ≤ (t : ℝ) * ρ ^ S := mul_le_mul_of_nonneg_right hs_le hρS0
    calc ((t - 1 : ℕ) : ℝ) * a ^ S = (d / 3) ^ S * (((t - 1 : ℕ) : ℝ) * ρ ^ S) := by
          rw [haS]; ring
      _ < (d / 3) ^ S * (1 / 2) := mul_lt_mul_of_pos_left (hle.trans_lt hlt) hd3
      _ = (d / 3) ^ S / 2 := by ring
  have h3' : ((t - 1 : ℕ) : ℝ) * (15 * S) ≤ d / 4 := by
    have hS0 : (0 : ℝ) ≤ 15 * S := by positivity
    have hsqL : 0 ≤ Real.sqrt L := Real.sqrt_nonneg _
    calc ((t - 1 : ℕ) : ℝ) * (15 * S) ≤ t * (15 * S) := mul_le_mul_of_nonneg_right hs_le hS0
      _ ≤ t * (15 * (49 * Real.sqrt L)) :=
          mul_le_mul_of_nonneg_left (by linarith) htpos.le
      _ = 735 * (t * Real.sqrt L) := by ring
      _ ≤ 12500 * (t * Real.sqrt L) := by nlinarith
      _ = d / 4 := by rw [hd]; ring
  obtain ⟨W1, -, hW1⟩ := dense_core H d hd100 hcard hdeg hne
  obtain ⟨B, hB⟩ := branch_sets H d hd100 hcard W1 hW1 S (t - 1) (by omega) a hapos h1 h2 h3'
  exact minor_of_branch H (t - 1) B hB

end asym

end KTLib

open HadwigerConj in
theorem solution :
    ∃ C : ℝ, ∀ t : ℕ, 1 ≤ t → ∀ (V : Type) [Finite V] (G : SimpleGraph V),
      ¬ HasCompleteMinor G t → G.Colorable ⌈C * t * Real.sqrt (Real.log t)⌉₊ := by
  exact KTLib.kt_of_denseLarge KTLib.dense_large
