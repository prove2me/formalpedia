-- Prove2me | solution 1 for NicerEars.TwoEC.theorem_30
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:58:05.684304+00:00
-- url     : https://prove2.me/submissions/e7a91677-0c76-4c65-b4c1-fa99224b605d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NicerEars_TwoEC_Setting
import Theorems.Thm_NicerEars_TwoEC_theorem_30_twoVertexConnected

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



lemma exists_not_mem {α : Type} [Fintype α] (s : Finset α) (h : #s < Fintype.card α) :
    ∃ c, c ∉ s := by
  by_contra hc; push Not at hc
  have : s = univ := eq_univ_iff_forall.mpr hc
  rw [this, card_univ] at h; omega

/-! ### Induced subgraphs on a vertex set -/

/-- Edges with both ends in `U`. -/
def EdgeIn (G : Graph V E) (U : Finset V) (e : E) : Prop := ∀ z, z ∈ G.ends e → z ∈ U

instance (G : Graph V E) (U : Finset V) : DecidablePred (EdgeIn G U) := by
  intro e; unfold EdgeIn; infer_instance

/-- Retraction of `V` onto `U` (identity on `U`). -/
def retr (U : Finset V) (u₀ : {w // w ∈ U}) (z : V) : {w // w ∈ U} :=
  if h : z ∈ U then ⟨z, h⟩ else u₀

lemma retr_val (U : Finset V) (u₀ : {w // w ∈ U}) (z : V) (h : z ∈ U) :
    (retr U u₀ z).val = z := by simp [retr, h]

lemma map_retr (G : Graph V E) (U : Finset V) (u₀ : {w // w ∈ U}) (e : {e // EdgeIn G U e}) :
    Sym2.map Subtype.val (Sym2.map (retr U u₀) (G.ends e.val)) = G.ends e.val := by
  rw [Sym2.map_map]
  have : Sym2.map (fun x : V => x) (G.ends e.val) = G.ends e.val := by rw [Sym2.map_id']; rfl
  conv_rhs => rw [← this]
  exact Sym2.map_congr (fun z hz => retr_val U u₀ z (e.prop z hz))

/-- The subgraph `G[U]` induced on `U`. -/
def sub (G : Graph V E) (U : Finset V) (u₀ : {w // w ∈ U}) :
    Graph {w // w ∈ U} {e // EdgeIn G U e} where
  ends e := Sym2.map (retr U u₀) (G.ends e.val)
  loopless e h := G.loopless e.val (by rw [← map_retr G U u₀ e]; exact h.map)

lemma sub_ends (G : Graph V E) (U : Finset V) (u₀ : {w // w ∈ U}) (e : {e // EdgeIn G U e})
    (a b : {w // w ∈ U}) : (sub G U u₀).ends e = s(a, b) ↔ G.ends e.val = s(a.val, b.val) := by
  constructor
  · intro h
    rw [← map_retr G U u₀ e]
    change Sym2.map Subtype.val ((sub G U u₀).ends e) = _
    rw [h]; rfl
  · intro h
    apply Sym2.map.injective Subtype.val_injective
    simp only [sub]
    rw [map_retr, h]; rfl


lemma edgeIn_iff (G : Graph V E) (U : Finset V) (e : E) (p q : V) (h : G.ends e = s(p, q)) :
    EdgeIn G U e ↔ p ∈ U ∧ q ∈ U := by
  unfold EdgeIn; rw [h]
  constructor
  · intro hz; exact ⟨hz p (Sym2.mem_mk_left _ _), hz q (Sym2.mem_mk_right _ _)⟩
  · rintro ⟨hp, hq⟩ z hz; rcases Sym2.mem_iff.1 hz with rfl | rfl <;> assumption

/-- Data of a split at a cut vertex `v`: `V \ {v} = A ∪ B` with no `A`–`B` edges. -/
structure Split (G : Graph V E) (v : V) (A B : Finset V) : Prop where
  vA : v ∉ A
  vB : v ∉ B
  cover : ∀ z, z = v ∨ z ∈ A ∨ z ∈ B
  disj : Disjoint A B
  sep : ∀ e p q, G.ends e = s(p, q) → p ∈ A → q ∉ B

lemma Split.symm {G : Graph V E} {v : V} {A B : Finset V} (h : Split G v A B) : Split G v B A where
  vA := h.vB
  vB := h.vA
  cover z := by rcases h.cover z with h1 | h1 | h1 <;> tauto
  disj := h.disj.symm
  sep e p q he hp hq := h.sep e q p (he.trans Sym2.eq_swap) hq hp


variable {G : Graph V E} {v : V} {A B : Finset V}

/-- The base vertex `v` of `insert v A`. -/
def base (v : V) (A : Finset V) : {w // w ∈ insert v A} := ⟨v, mem_insert_self v A⟩

/-- The lift of a vertex set `W` of `G[A ∪ {v}]` to `V`: add `B` when `v ∈ W`. -/
def liftSet (v : V) (A B : Finset V) (W : Finset {w // w ∈ insert v A}) : Finset V :=
  W.map (Function.Embedding.subtype _) ∪ (if base v A ∈ W then B else ∅)

lemma mem_liftSet (W : Finset {w // w ∈ insert v A}) (z : V) :
    z ∈ liftSet v A B W ↔ (∃ h : z ∈ insert v A, ⟨z, h⟩ ∈ W) ∨ (base v A ∈ W ∧ z ∈ B) := by
  unfold liftSet
  rw [mem_union]
  apply or_congr
  · simp [mem_map]
  · split_ifs with h <;> simp [h]

lemma cut_liftSet (hS : Split G v A B) (W : Finset {w // w ∈ insert v A}) (e : E) :
    e ∈ G.cut (liftSet v A B W) ↔
      ∃ h : EdgeIn G (insert v A) e, ⟨e, h⟩ ∈ (sub G (insert v A) (base v A)).cut W := by
  have hUB : ∀ z, z ∈ insert v A → z ∉ B := by
    intro z hz hzB
    rcases mem_insert.1 hz with rfl | hzA
    · exact hS.vB hzB
    · exact disjoint_left.1 hS.disj hzA hzB
  constructor
  · intro he
    obtain ⟨p, hp, q, hq, hends⟩ := (mem_cut G _ e).1 he
    rw [mem_liftSet] at hp hq
    push Not at hq
    rcases hp with ⟨hpU, hpW⟩ | ⟨hvW, hpB⟩
    · -- p ∈ W
      have hqB : q ∉ B := by
        intro hqB
        by_cases hvW : base v A ∈ W
        · exact (hq.2 hvW) hqB
        · have hpv : p ≠ v := by
            rintro rfl; exact hvW hpW
          have hpA : p ∈ A := (mem_insert.1 hpU).resolve_left hpv
          exact hS.sep e p q hends hpA hqB
      have hqU : q ∈ insert v A := by
        rcases hS.cover q with h1 | h1 | h1
        · exact h1 ▸ mem_insert_self _ _
        · exact mem_insert_of_mem h1
        · exact absurd h1 hqB
      have hE : EdgeIn G (insert v A) e := (edgeIn_iff G _ e p q hends).2 ⟨hpU, hqU⟩
      refine ⟨hE, ?_⟩
      rw [mem_cut]
      exact ⟨⟨p, hpU⟩, hpW, ⟨q, hqU⟩, hq.1 hqU, (sub_ends G _ _ ⟨e, hE⟩ _ _).2 hends⟩
    · -- p ∈ B, v ∈ W
      exfalso
      have hqB : q ∉ B := hq.2 hvW
      have hqv : q ≠ v := by
        rintro rfl; exact hq.1 (mem_insert_self _ _) hvW
      have hqA : q ∈ A := by
        rcases hS.cover q with h1 | h1 | h1
        · exact absurd h1 hqv
        · exact h1
        · exact absurd h1 hqB
      exact hS.sep e q p (hends.trans Sym2.eq_swap) hqA hpB
  · rintro ⟨hE, he⟩
    obtain ⟨a, ha, b, hb, hends⟩ := (mem_cut _ W _).1 he
    rw [sub_ends] at hends
    refine (mem_cut G _ e).2 ⟨a.val, ?_, b.val, ?_, hends⟩
    · rw [mem_liftSet]; exact Or.inl ⟨a.prop, ha⟩
    · rw [mem_liftSet]; push Not
      exact ⟨fun _ => hb, fun _ => hUB b.val b.prop⟩

lemma liftSet_nonempty (W : Finset {w // w ∈ insert v A}) (hW : W.Nonempty) :
    (liftSet v A B W).Nonempty := by
  obtain ⟨a, ha⟩ := hW
  exact ⟨a.val, (mem_liftSet W _).2 (Or.inl ⟨a.prop, ha⟩)⟩

lemma liftSet_ne_univ (hS : Split G v A B) (W : Finset {w // w ∈ insert v A}) (hW : W ≠ univ) :
    liftSet v A B W ≠ univ := by
  obtain ⟨c, hc⟩ := exists_not_mem W (by
    have := card_le_univ W
    have : #W ≠ Fintype.card {w // w ∈ insert v A} := fun hh => hW (eq_univ_of_card W hh)
    omega)
  intro hh
  have : c.val ∈ liftSet v A B W := hh ▸ mem_univ _
  rw [mem_liftSet] at this
  rcases this with ⟨_, h⟩ | ⟨_, hB⟩
  · exact hc h
  · rcases mem_insert.1 c.prop with h1 | h1
    · exact hS.vB (h1 ▸ hB)
    · exact disjoint_left.1 hS.disj h1 hB

lemma cut_liftSet_eq (hS : Split G v A B) (W : Finset {w // w ∈ insert v A}) :
    G.cut (liftSet v A B W) =
      ((sub G (insert v A) (base v A)).cut W).map (Function.Embedding.subtype _) := by
  ext e
  rw [cut_liftSet hS, mem_map]
  constructor
  · rintro ⟨h, he⟩; exact ⟨⟨e, h⟩, he, rfl⟩
  · rintro ⟨e', he', rfl⟩; exact ⟨e'.prop, he'⟩

lemma sub_twoEC (hS : Split G v A B) (hG : G.IsTwoEdgeConnected) :
    (sub G (insert v A) (base v A)).IsTwoEdgeConnected := by
  have : Nonempty V := ⟨v⟩
  have : Nonempty {w // w ∈ insert v A} := ⟨base v A⟩
  unfold Graph.IsTwoEdgeConnected at hG ⊢
  rw [twoEC_iff_cut] at hG ⊢
  intro W hW hWu
  obtain ⟨e₁, -, e₂, -, hne, h₁, h₂⟩ :=
    hG _ (liftSet_nonempty (B := B) W hW) (liftSet_ne_univ hS W hWu)
  obtain ⟨k₁, h₁⟩ := (cut_liftSet hS W e₁).1 h₁
  obtain ⟨k₂, h₂⟩ := (cut_liftSet hS W e₂).1 h₂
  exact ⟨_, mem_univ _, _, mem_univ _, fun h => hne (congrArg Subtype.val h), h₁, h₂⟩

lemma sub_feasible (hS : Split G v A B) (x : E → ℝ) (hx : G.LPFeasible x) :
    (sub G (insert v A) (base v A)).LPFeasible (fun e => x e.val) := by
  refine ⟨fun e => hx.1 _, fun W hW hWu => ?_⟩
  have := hx.2 _ (liftSet_nonempty (B := B) W hW) (liftSet_ne_univ hS W hWu)
  rw [cut_liftSet_eq hS, sum_map] at this
  simpa using this

/-- A 2-edge-connected subgraph of `G[U]` covers every cut of `G` that separates `U`. -/
lemma lift_twoEC (U : Finset V) (u₀ : {w // w ∈ U}) (F : Finset {e // EdgeIn G U e})
    (hF : (sub G U u₀).IsTwoECSpanning F) (W : Finset V) (a b : {w // w ∈ U})
    (ha : a.val ∈ W) (hb : b.val ∉ W) :
    ∃ e₁ ∈ F.map (Function.Embedding.subtype _), ∃ e₂ ∈ F.map (Function.Embedding.subtype _),
      e₁ ≠ e₂ ∧ e₁ ∈ G.cut W ∧ e₂ ∈ G.cut W := by
  have : Nonempty {w // w ∈ U} := ⟨u₀⟩
  rw [twoEC_iff_cut] at hF
  let W₁ : Finset {w // w ∈ U} := univ.filter (fun z => z.val ∈ W)
  have hW₁ : W₁.Nonempty := ⟨a, by simp [W₁, ha]⟩
  have hW₁u : W₁ ≠ univ := by
    intro hh
    have : b ∈ W₁ := hh ▸ mem_univ b
    simp [W₁] at this; exact hb this
  obtain ⟨f₁, hf₁, f₂, hf₂, hne, h₁, h₂⟩ := hF W₁ hW₁ hW₁u
  have tr : ∀ f : {e // EdgeIn G U e}, f ∈ (sub G U u₀).cut W₁ → f.val ∈ G.cut W := by
    intro f hf
    obtain ⟨p, hp, q, hq, hends⟩ := (mem_cut _ _ _).1 hf
    rw [sub_ends] at hends
    simp only [W₁, mem_filter, mem_univ, true_and] at hp hq
    exact cut_of_ends G W _ _ _ hends hp hq
  exact ⟨f₁.val, mem_map_of_mem _ hf₁, f₂.val, mem_map_of_mem _ hf₂,
    fun h => hne (Subtype.ext h), tr f₁ h₁, tr f₂ h₂⟩


lemma edgeIn_compl (hS : Split G v A B) (e : E) :
    EdgeIn G (insert v B) e ↔ ¬ EdgeIn G (insert v A) e := by
  obtain ⟨p, q, hpq, hends⟩ := ends_eq G e
  rw [edgeIn_iff G _ e p q hends, edgeIn_iff G _ e p q hends]
  have fA : ∀ z, z ∈ A → z ∈ insert v A ∧ z ∉ insert v B := by
    intro z hz
    refine ⟨mem_insert_of_mem hz, ?_⟩
    rw [mem_insert, not_or]
    exact ⟨fun h => hS.vA (h ▸ hz), disjoint_left.1 hS.disj hz⟩
  have fB : ∀ z, z ∈ B → z ∈ insert v B ∧ z ∉ insert v A := by
    intro z hz
    refine ⟨mem_insert_of_mem hz, ?_⟩
    rw [mem_insert, not_or]
    exact ⟨fun h => hS.vB (h ▸ hz), disjoint_right.1 hS.disj hz⟩
  have fv1 : v ∈ insert v A := mem_insert_self _ _
  have fv2 : v ∈ insert v B := mem_insert_self _ _
  rcases hS.cover p with rfl | hp | hp <;> rcases hS.cover q with rfl | hq | hq
  · exact absurd rfl hpq
  · have := fA q hq; tauto
  · have := fB q hq; tauto
  · have := fA p hp; tauto
  · have := fA p hp; have := fA q hq; tauto
  · exact absurd hq (hS.sep e p q hends hp)
  · have := fB p hp; tauto
  · exact absurd hp (hS.sep e q p (hends.trans Sym2.eq_swap) hq)
  · have := fB p hp; have := fB q hq; tauto

lemma sum_split (hS : Split G v A B) (x : E → ℝ) :
    ∑ e, x e = ∑ e : {e // EdgeIn G (insert v A) e}, x e.val +
      ∑ e : {e // EdgeIn G (insert v B) e}, x e.val := by
  rw [← sum_filter_add_sum_filter_not univ (EdgeIn G (insert v A))]
  congr 1
  · exact Finset.sum_subtype _ (fun e => by simp) _
  · exact Finset.sum_subtype _ (fun e => by simp [edgeIn_compl hS e]) _

lemma split_combine (hS : Split G v A B)
    (F₁ : Finset {e // EdgeIn G (insert v A) e})
    (hF₁ : (sub G (insert v A) (base v A)).IsTwoECSpanning F₁)
    (hb₁ : ∀ x, (sub G (insert v A) (base v A)).LPFeasible x → (#F₁ : ℝ) ≤ 4 / 3 * ∑ e, x e)
    (F₂ : Finset {e // EdgeIn G (insert v B) e})
    (hF₂ : (sub G (insert v B) (base v B)).IsTwoECSpanning F₂)
    (hb₂ : ∀ x, (sub G (insert v B) (base v B)).LPFeasible x → (#F₂ : ℝ) ≤ 4 / 3 * ∑ e, x e) :
    ∃ F : Finset E, G.IsTwoECSpanning F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 4 / 3 * ∑ e, x e := by
  have : Nonempty V := ⟨v⟩
  refine ⟨F₁.map (Function.Embedding.subtype _) ∪ F₂.map (Function.Embedding.subtype _), ?_, ?_⟩
  · rw [twoEC_iff_cut]
    intro W hW hWu
    have up1 : ∀ e ∈ F₁.map (Function.Embedding.subtype _),
        e ∈ F₁.map (Function.Embedding.subtype _) ∪ F₂.map (Function.Embedding.subtype _) :=
      fun e he => mem_union_left _ he
    have up2 : ∀ e ∈ F₂.map (Function.Embedding.subtype _),
        e ∈ F₁.map (Function.Embedding.subtype _) ∪ F₂.map (Function.Embedding.subtype _) :=
      fun e he => mem_union_right _ he
    have fin1 : ∀ a b : {w // w ∈ insert v A}, a.val ∈ W → b.val ∉ W → ∃ e₁ ∈
        F₁.map (Function.Embedding.subtype _) ∪ F₂.map (Function.Embedding.subtype _), ∃ e₂ ∈
        F₁.map (Function.Embedding.subtype _) ∪ F₂.map (Function.Embedding.subtype _),
        e₁ ≠ e₂ ∧ e₁ ∈ G.cut W ∧ e₂ ∈ G.cut W := by
      intro a b ha hb
      obtain ⟨e₁, h₁, e₂, h₂, hne, c₁, c₂⟩ := lift_twoEC _ (base v A) F₁ hF₁ W a b ha hb
      exact ⟨e₁, up1 _ h₁, e₂, up1 _ h₂, hne, c₁, c₂⟩
    have fin2 : ∀ a b : {w // w ∈ insert v B}, a.val ∈ W → b.val ∉ W → ∃ e₁ ∈
        F₁.map (Function.Embedding.subtype _) ∪ F₂.map (Function.Embedding.subtype _), ∃ e₂ ∈
        F₁.map (Function.Embedding.subtype _) ∪ F₂.map (Function.Embedding.subtype _),
        e₁ ≠ e₂ ∧ e₁ ∈ G.cut W ∧ e₂ ∈ G.cut W := by
      intro a b ha hb
      obtain ⟨e₁, h₁, e₂, h₂, hne, c₁, c₂⟩ := lift_twoEC _ (base v B) F₂ hF₂ W a b ha hb
      exact ⟨e₁, up2 _ h₁, e₂, up2 _ h₂, hne, c₁, c₂⟩
    by_cases hvW : v ∈ W
    · by_cases h1 : ∃ b : {w // w ∈ insert v A}, b.val ∉ W
      · obtain ⟨b, hb⟩ := h1; exact fin1 (base v A) b hvW hb
      by_cases h2 : ∃ b : {w // w ∈ insert v B}, b.val ∉ W
      · obtain ⟨b, hb⟩ := h2; exact fin2 (base v B) b hvW hb
      exfalso; apply hWu; apply eq_univ_iff_forall.mpr
      intro z
      push Not at h1 h2
      rcases hS.cover z with rfl | hz | hz
      · exact hvW
      · exact h1 ⟨z, mem_insert_of_mem hz⟩
      · exact h2 ⟨z, mem_insert_of_mem hz⟩
    · by_cases h1 : ∃ a : {w // w ∈ insert v A}, a.val ∈ W
      · obtain ⟨a, ha⟩ := h1; exact fin1 a (base v A) ha hvW
      by_cases h2 : ∃ a : {w // w ∈ insert v B}, a.val ∈ W
      · obtain ⟨a, ha⟩ := h2; exact fin2 a (base v B) ha hvW
      exfalso
      obtain ⟨z, hz⟩ := hW
      push Not at h1 h2
      rcases hS.cover z with rfl | hz' | hz'
      · exact hvW hz
      · exact h1 ⟨z, mem_insert_of_mem hz'⟩ hz
      · exact h2 ⟨z, mem_insert_of_mem hz'⟩ hz
  · intro x hx
    have h1 := hb₁ _ (sub_feasible hS x hx)
    have h2 := hb₂ _ (sub_feasible hS.symm x hx)
    have hc : (#(F₁.map (Function.Embedding.subtype _) ∪ F₂.map (Function.Embedding.subtype _)) : ℝ)
        ≤ #F₁ + #F₂ := by
      have := card_union_le (F₁.map (Function.Embedding.subtype _))
        (F₂.map (Function.Embedding.subtype _))
      rw [card_map, card_map] at this
      exact_mod_cast this
    rw [sum_split hS x]
    linarith

lemma exists_split (G : Graph V E) (h2 : ¬ G.IsTwoVertexConnected) (hG : G.IsTwoEdgeConnected) :
    ∃ v A B, Split G v A B ∧ A.Nonempty ∧ B.Nonempty := by
  classical
  unfold Graph.IsTwoVertexConnected at h2
  push Not at h2
  obtain ⟨v, hv⟩ := h2 hG
  unfold SimpleGraph.Preconnected at hv
  push Not at hv
  obtain ⟨a, b, hab⟩ := hv
  let H := (G.spanGraph univ).induce {w | w ≠ v}
  let A : Finset V := univ.filter (fun z => ∃ h : z ≠ v, H.Reachable a ⟨z, h⟩)
  let B : Finset V := univ.filter (fun z => ∃ h : z ≠ v, ¬ H.Reachable a ⟨z, h⟩)
  refine ⟨v, A, B, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨a.val, ?_⟩, ⟨b.val, ?_⟩⟩
  · simp [A]
  · simp [B]
  · intro z
    by_cases hz : z = v
    · exact Or.inl hz
    · by_cases hr : H.Reachable a ⟨z, hz⟩
      · exact Or.inr (Or.inl (by simp only [A, mem_filter, mem_univ, true_and]; exact ⟨hz, hr⟩))
      · exact Or.inr (Or.inr (by simp only [B, mem_filter, mem_univ, true_and]; exact ⟨hz, hr⟩))
  · rw [disjoint_left]
    intro z hzA hzB
    simp only [A, B, mem_filter, mem_univ, true_and] at hzA hzB
    obtain ⟨h1, r⟩ := hzA
    obtain ⟨h2, nr⟩ := hzB
    exact nr r
  · intro e p q hends hp hq
    simp only [A, B, mem_filter, mem_univ, true_and] at hp hq
    obtain ⟨hp, rp⟩ := hp
    obtain ⟨hq', nq⟩ := hq
    have hpq : p ≠ q := by
      rintro rfl; exact G.loopless e (by rw [hends]; exact Sym2.mk_isDiag_iff.2 rfl)
    have hadj : H.Adj ⟨p, hp⟩ ⟨q, hq'⟩ := by
      rw [SimpleGraph.induce_adj, spanGraph_adj]
      exact ⟨hpq, e, mem_univ _, hends⟩
    exact nq (rp.trans hadj.reachable)
  · simp only [A, mem_filter, mem_univ, true_and]
    exact ⟨a.prop, SimpleGraph.Reachable.refl _⟩
  · simp only [B, mem_filter, mem_univ, true_and]
    exact ⟨b.prop, hab⟩

lemma card_insert_lt (hS : Split G v A B) (hB : B.Nonempty) :
    Fintype.card {w // w ∈ insert v A} < Fintype.card V := by
  rw [Fintype.card_coe, ← card_univ]
  apply card_lt_card
  rw [ssubset_univ_iff]
  intro h
  obtain ⟨b, hb⟩ := hB
  have : b ∈ insert v A := h ▸ mem_univ b
  rcases mem_insert.1 this with rfl | h'
  · exact hS.vB hb
  · exact disjoint_left.1 hS.disj h' hb

theorem reduce : ∀ (n : ℕ) (V E : Type) [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : Graph V E), Fintype.card V = n → G.IsTwoEdgeConnected →
    ∃ F : Finset E, G.IsTwoECSpanning F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 4 / 3 * ∑ e, x e := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V E _ _ _ _ G hn hG
    by_cases h2 : G.IsTwoVertexConnected
    · exact theorem_30_twoVertexConnected G h2
    · obtain ⟨v, A, B, hS, hA, hB⟩ := exists_split G h2 hG
      obtain ⟨F₁, hF₁, hb₁⟩ := ih _ (hn ▸ card_insert_lt hS hB) _ _
        (sub G (insert v A) (base v A)) rfl (sub_twoEC hS hG)
      obtain ⟨F₂, hF₂, hb₂⟩ := ih _ (hn ▸ card_insert_lt hS.symm hA) _ _
        (sub G (insert v B) (base v B)) rfl (sub_twoEC hS.symm hG)
      exact split_combine hS F₁ hF₁ hb₁ F₂ hF₂ hb₂

end NicerEars.TwoEC.Aux30

open Finset in
theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : NicerEars.TwoEC.Graph V E) (hG : G.IsTwoEdgeConnected) :
    ∃ F : Finset E, G.IsTwoECSpanning F ∧
      ∀ x : E → ℝ, G.LPFeasible x → (#F : ℝ) ≤ 4 / 3 * ∑ e, x e :=
  NicerEars.TwoEC.Aux30.reduce _ V E G rfl hG
