-- Prove2me | solution 1 for MetricTSPSublinear.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:21:16.04604+00:00
-- url     : https://prove2.me/submissions/c95d64d5-9501-4098-9329-df6f64b02021

import Mathlib
import Definitions.Def_MetricTSPSublinear_IsSubtree

namespace MTSPHelly
open SimpleGraph MetricTSPSublinear

section Graph
variable {V : Type*} {G : SimpleGraph V}

lemma reach_or_reach_aux {a b : V} : ∀ (w t : V) (_p : G.Walk w t), t = a →
    (G.deleteEdges {s(a, b)}).Reachable w a ∨ (G.deleteEdges {s(a, b)}).Reachable w b := by
  intro w t p
  induction p with
  | nil => intro h; subst h; exact Or.inl (Reachable.refl _)
  | @cons u u' _ h p ih =>
    intro ht
    have ih := ih ht
    by_cases he : s(u, u') = s(a, b)
    · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl (Reachable.refl _)
      · exact Or.inr (Reachable.refl _)
    · have hadj : (G.deleteEdges {s(a, b)}).Adj u u' := by
        rw [deleteEdges_adj]; exact ⟨h, by simpa using he⟩
      rcases ih with h1 | h1
      · exact Or.inl (hadj.reachable.trans h1)
      · exact Or.inr (hadj.reachable.trans h1)

lemma reach_or_reach (hconn : G.Connected) {a b : V} (w : V) :
    (G.deleteEdges {s(a, b)}).Reachable w a ∨ (G.deleteEdges {s(a, b)}).Reachable w b := by
  obtain ⟨p⟩ := hconn.preconnected w a
  exact reach_or_reach_aux w a p rfl

lemma not_reach_of_adj (hac : G.IsAcyclic) {a b : V} (hadj : G.Adj a b) :
    ¬ (G.deleteEdges {s(a, b)}).Reachable a b :=
  isAcyclic_iff_forall_adj_isBridge.mp hac hadj

/-- In a tree, an edge lies on the path between `u` and `v` iff deleting it separates them. -/
lemma mem_path_edges_iff (hT : G.IsTree) {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (e : Sym2 V) : e ∈ p.edges ↔ ¬ (G.deleteEdges {e}).Reachable u v := by
  classical
  constructor
  · intro he hR
    obtain ⟨q⟩ := hR
    let q' := q.toPath
    have hq'p : (q'.val.mapLe (G.deleteEdges_le {e})).IsPath := q'.property.mapLe _
    have heq : q'.val.mapLe (G.deleteEdges_le {e}) = p := by
      have := (hT.existsUnique_path u v).unique hq'p hp
      exact this
    rw [← heq, Walk.edges_mapLe_eq_edges] at he
    have := q'.val.edges_subset_edgeSet he
    rw [edgeSet_deleteEdges] at this
    exact this.2 rfl
  · intro hR
    by_contra he
    exact hR ⟨p.toDeleteEdge e he⟩

end Graph

section Arith

lemma arith1 (α γ S : ℝ) (hα : 0 < α ∧ α < 1) (hγ : γ = 0 ∨ γ = 1) :
    min (α + (|0 - γ| + S)) ((1 - α) + (|1 - γ| + S)) = |γ - α| + S := by
  have h1 : |α| = α := abs_of_pos hα.1
  have h2 : |1 - α| = 1 - α := abs_of_pos (by linarith)
  rcases hγ with rfl | rfl <;> norm_num [h1, h2, abs_sub_comm 1 α] <;> linarith

lemma arith2 (α β γ δ S : ℝ) (hα : 0 < α ∧ α < 1) (hβ : 0 < β ∧ β < 1) (hγ : γ = 0 ∨ γ = 1)
    (hδ : δ = 0 ∨ δ = 1) :
    min (min (α + (|0 - γ| + |δ - 0| + S) + β) (α + (|0 - γ| + |δ - 1| + S) + (1 - β)))
        (min ((1 - α) + (|1 - γ| + |δ - 0| + S) + β) ((1 - α) + (|1 - γ| + |δ - 1| + S) + (1 - β)))
      = |α - γ| + |δ - β| + S := by
  have h1 : |α| = α := abs_of_pos hα.1
  have h2 : |1 - α| = 1 - α := abs_of_pos (by linarith)
  have h3 : |β| = β := abs_of_pos hβ.1
  have h4 : |1 - β| = 1 - β := abs_of_pos (by linarith)
  rcases hγ with rfl | rfl <;> rcases hδ with rfl | rfl <;>
    norm_num [h1, h2, h3, h4, abs_sub_comm 1 α, abs_sub_comm α 1, abs_sub_comm 1 β, abs_sub_comm β 1] <;>
    simp only [min_def] <;> split_ifs <;> linarith

end Arith

section Between

/-- `t` lies between `x` and `y` (on the real line). -/
def Bt (x y t : ℝ) : Prop := |x - t| + |t - y| = |x - y|

lemma btw_iff {x y t : ℝ} : Bt x y t ↔ (x ≤ t ∧ t ≤ y) ∨ (y ≤ t ∧ t ≤ x) := by
  unfold Bt
  constructor
  · intro h
    rcases le_total x t with h1 | h1 <;> rcases le_total t y with h2 | h2
    · exact Or.inl ⟨h1, h2⟩
    · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
      rcases le_total x y with h3 | h3
      · rw [abs_of_nonpos (by linarith)] at h; exact Or.inl ⟨h1, by linarith⟩
      · rw [abs_of_nonneg (by linarith)] at h; exact Or.inr ⟨by linarith, by linarith⟩
    · rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h
      rcases le_total x y with h3 | h3
      · rw [abs_of_nonpos (by linarith)] at h; exact Or.inl ⟨by linarith, by linarith⟩
      · rw [abs_of_nonneg (by linarith)] at h; exact Or.inr ⟨by linarith, h1⟩
    · exact Or.inr ⟨h2, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      ring

lemma btw_left (x y : ℝ) : Bt x y x := btw_iff.mpr (by rcases le_total x y with h | h <;> simp [h])
lemma btw_right (x y : ℝ) : Bt x y y := btw_iff.mpr (by rcases le_total x y with h | h <;> simp [h])
lemma btw_self (x : ℝ) : Bt x x x := btw_left x x
lemma btw_symm {x y t : ℝ} (h : Bt x y t) : Bt y x t := by
  rw [btw_iff] at *; tauto

lemma btw_trans {p q y x : ℝ} (h1 : Bt p q y) (h2 : Bt y q x) : Bt p q x := by
  rw [btw_iff] at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ <;>
    first | (left; constructor <;> linarith) | (right; constructor <;> linarith)

lemma btw_conv {a b p q r : ℝ} (h1 : Bt a b p) (h2 : Bt q r a) (h3 : Bt q r b) : Bt q r p := by
  rw [btw_iff] at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h3 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases le_total q r with _ | _ <;>
    first | (left; constructor <;> linarith) | (right; constructor <;> linarith)

lemma btw_lift {c d q r t : ℝ} (h1 : Bt c d q) (h2 : Bt c r t) (h3 : Bt d r t) : Bt q r t := by
  rw [btw_iff] at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ <;>
    rcases h3 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases le_total q t with _ | _ <;>
    first | (left; constructor <;> linarith) | (right; constructor <;> linarith)

lemma btw_med3 (α β γ : ℝ) :
    (Bt α β α ∧ Bt β γ α ∧ Bt α γ α) ∨ (Bt α β β ∧ Bt β γ β ∧ Bt α γ β) ∨
      (Bt α β γ ∧ Bt β γ γ ∧ Bt α γ γ) := by
  simp only [btw_iff]
  rcases le_total α β with _ | _ <;> rcases le_total β γ with _ | _ <;>
    rcases le_total α γ with _ | _ <;>
    first
    | (left; refine ⟨?_, ?_, ?_⟩ <;>
        first | (left; constructor <;> linarith) | (right; constructor <;> linarith))
    | (right; left; refine ⟨?_, ?_, ?_⟩ <;>
        first | (left; constructor <;> linarith) | (right; constructor <;> linarith))
    | (right; right; refine ⟨?_, ?_, ?_⟩ <;>
        first | (left; constructor <;> linarith) | (right; constructor <;> linarith))

/-- For `0/1` values betweenness fails only if the two ends agree and the middle differs. -/
lemma btw_01 {x y t : ℝ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) (ht : t = 0 ∨ t = 1) :
    Bt x y t ↔ ¬ (x = y ∧ t ≠ x) := by
  rw [btw_iff]
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> rcases ht with rfl | rfl <;> norm_num

end Between

section Sides
variable {m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.IsTree)

/-- The edges of `G`, as ordered pairs with the smaller end first. -/
noncomputable def Es : Finset (Fin m × Fin m) := by
  classical exact Finset.univ.filter (fun x => x.1 < x.2 ∧ G.Adj x.1 x.2)

lemma mem_Es {e : Fin m × Fin m} : e ∈ Es G ↔ e.1 < e.2 ∧ G.Adj e.1 e.2 := by
  classical simp [Es]

/-- The side of `v` with respect to the edge `e = (a, b)`: `0` on the side of `a`, `1` on the side of `b`. -/
noncomputable def sd (e : Fin m × Fin m) (v : Fin m) : ℝ := by
  classical exact if (G.deleteEdges {s(e.1, e.2)}).Reachable e.1 v then 0 else 1

lemma sd_01 (e : Fin m × Fin m) (v : Fin m) : sd G e v = 0 ∨ sd G e v = 1 := by
  unfold sd; split_ifs <;> simp

include hG in
lemma sd_eq_iff {e : Fin m × Fin m} (he : e ∈ Es G) (u v : Fin m) :
    sd G e u = sd G e v ↔ (G.deleteEdges {s(e.1, e.2)}).Reachable u v := by
  rw [mem_Es] at he
  have hab := not_reach_of_adj hG.isAcyclic he.2
  have hu := reach_or_reach hG.connected (a := e.1) (b := e.2) u
  have hv := reach_or_reach hG.connected (a := e.1) (b := e.2) v
  unfold sd
  set R := (G.deleteEdges {s(e.1, e.2)}).Reachable
  split_ifs with h1 h2 h2
  · simp only [true_iff]; exact h1.symm.trans h2
  · simp only [zero_ne_one, false_iff]; intro h; exact h2 (h1.trans h)
  · simp only [one_ne_zero, false_iff]; intro h; exact h1 (h2.trans h.symm)
  · simp only [true_iff]
    have hu' : R u e.2 := hu.resolve_left (fun h => h1 h.symm)
    have hv' : R v e.2 := hv.resolve_left (fun h => h2 h.symm)
    exact hu'.trans hv'.symm

lemma sd_fst {e : Fin m × Fin m} : sd G e e.1 = 0 := by
  unfold sd; simp

include hG in
lemma sd_snd {e : Fin m × Fin m} (he : e ∈ Es G) : sd G e e.2 = 1 := by
  rw [mem_Es] at he
  unfold sd; simp [not_reach_of_adj hG.isAcyclic he.2]

include hG in
lemma sd_adj {e : Fin m × Fin m} (he : e ∈ Es G) {a b : Fin m} (hab : G.Adj a b)
    (hne : s(a, b) ≠ s(e.1, e.2)) : sd G e a = sd G e b := by
  rw [sd_eq_iff G hG he]
  apply Adj.reachable
  rw [deleteEdges_adj]; exact ⟨hab, by simpa using hne⟩

lemma pair_ne_of_ne {e f : Fin m × Fin m} (he : e ∈ Es G) (hf : f ∈ Es G) (hne : f ≠ e) :
    s(f.1, f.2) ≠ s(e.1, e.2) := by
  rw [mem_Es] at he hf
  intro h
  rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hne (Prod.ext h1 h2)
  · have h3 := hf.1; rw [h1, h2] at h3; exact absurd (lt_trans he.1 h3) (lt_irrefl _)

include hG in
/-- The key separation lemma: if `e` does not separate `q` and `r` but `f` does, then both ends of `f`
are on the side of `q` with respect to `e`. -/
lemma sep {e f : Fin m × Fin m} (he : e ∈ Es G) (hf : f ∈ Es G) {q r : Fin m}
    (h1 : sd G e q = sd G e r) (h2 : sd G f q ≠ sd G f r) :
    sd G e f.1 = sd G e q ∧ sd G e f.2 = sd G e q := by
  classical
  rw [sd_eq_iff G hG he] at h1
  obtain ⟨W⟩ := h1
  let W' : G.Walk q r := W.mapLe (G.deleteEdges_le _)
  by_cases hmem : s(f.1, f.2) ∈ W'.edges
  · have hs1 : f.1 ∈ W.support := by
      rw [← Walk.support_mapLe_eq_support (G.deleteEdges_le _)]
      exact W'.fst_mem_support_of_mem_edges hmem
    have hs2 : f.2 ∈ W.support := by
      rw [← Walk.support_mapLe_eq_support (G.deleteEdges_le _)]
      exact W'.snd_mem_support_of_mem_edges hmem
    obtain ⟨W1, _, _⟩ := Walk.mem_support_iff_exists_append.mp hs1
    obtain ⟨W2, _, _⟩ := Walk.mem_support_iff_exists_append.mp hs2
    exact ⟨((sd_eq_iff G hG he _ _).mpr ⟨W1⟩).symm, ((sd_eq_iff G hG he _ _).mpr ⟨W2⟩).symm⟩
  · exact absurd ((sd_eq_iff G hG hf _ _).mpr ⟨W'.toDeleteEdge _ hmem⟩) h2

lemma abs_sd_sub (e : Fin m × Fin m) (u v : Fin m) :
    |sd G e u - sd G e v| = if sd G e u = sd G e v then 0 else 1 := by
  rcases sd_01 G e u with h1 | h1 <;> rcases sd_01 G e v with h2 | h2 <;> simp [h1, h2]

include hG in
lemma dist_eq_sum (u v : Fin m) :
    (unitTree G hG).dist u v = ∑ e ∈ Es G, |sd G e u - sd G e v| := by
  classical
  let p : G.Walk u v := (unitTree G hG).path u v
  have hp : p.IsPath := ((unitTree G hG).isTree.existsUnique_path u v).exists.choose_spec
  have h1 : (unitTree G hG).dist u v = (p.length : ℝ) := by
    simp only [TreeCoverLB.WeightedTree.dist, KServer.walkWeight, unitTree, List.map_const',
      List.sum_replicate, Walk.length_darts, nsmul_eq_mul, mul_one]
    rfl
  rw [h1, ← Walk.length_edges]
  have h2 : ∀ e ∈ Es G, |sd G e u - sd G e v| =
      if s(e.1, e.2) ∈ p.edges then (1 : ℝ) else 0 := by
    intro e he
    have h3 := sd_eq_iff G hG he u v
    have h4 := mem_path_edges_iff hG p hp (s(e.1, e.2))
    rw [abs_sd_sub]
    by_cases h : sd G e u = sd G e v
    · rw [if_pos h, if_neg (by rw [h4, not_not]; exact h3.mp h)]
    · rw [if_neg h, if_pos (by rw [h4]; exact fun h' => h (h3.mpr h'))]
  rw [Finset.sum_congr rfl h2, Finset.sum_boole]
  have h3 : ((Es G).filter (fun e => s(e.1, e.2) ∈ p.edges)).image (fun e => s(e.1, e.2)) =
      p.edges.toFinset := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨e, ⟨_, he⟩, rfl⟩; exact he
    · intro hx
      have hxG : x ∈ G.edgeSet := p.edges_subset_edgeSet hx
      induction x using Sym2.ind with
      | h x y =>
        have hxy : G.Adj x y := hxG
        rcases lt_or_gt_of_ne hxy.ne with hlt | hlt
        · exact ⟨(x, y), ⟨(mem_Es G).mpr ⟨hlt, hxy⟩, hx⟩, rfl⟩
        · exact ⟨(y, x), ⟨(mem_Es G).mpr ⟨hlt, hxy.symm⟩, by simpa [Sym2.eq_swap] using hx⟩,
            Sym2.eq_swap⟩
  have h4 : ((Es G).filter (fun e => s(e.1, e.2) ∈ p.edges)).card = p.edges.toFinset.card := by
    rw [← h3, Finset.card_image_of_injOn]
    intro e he f hf hef
    by_contra hne
    exact pair_ne_of_ne G (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp hf).1 (Ne.symm hne)
      hef.symm
  rw [h4, List.toFinset_card_of_nodup hp.isTrail.edges_nodup]

lemma sd_nonneg (e : Fin m × Fin m) (v : Fin m) : 0 ≤ sd G e v := by
  rcases sd_01 G e v with h | h <;> norm_num [h]

lemma sd_le_one (e : Fin m × Fin m) (v : Fin m) : sd G e v ≤ 1 := by
  rcases sd_01 G e v with h | h <;> norm_num [h]

/-- The (unit-weight) tree distance between vertices, as a sum over edges. -/
noncomputable def DD (u v : Fin m) : ℝ := ∑ e ∈ Es G, |sd G e u - sd G e v|

lemma unitTree_w (e : Sym2 (Fin m)) : (unitTree G hG).w e = 1 := rfl

lemma ud_vv (u v : Fin m) : unitDist G hG (.vtx u) (.vtx v) = DD G u v := by
  simp only [unitDist, rdist, dist_eq_sum G hG, DD]

lemma ud_vi (c a b : Fin m) (h1 h2 α hα) : unitDist G hG (.vtx c) (.inner a b h1 h2 α hα) =
    min (α + DD G a c) ((1 - α) + DD G b c) := by
  simp only [unitDist, rdist, dist_eq_sum G hG, DD, unitTree_w, mul_one]

lemma ud_iv (c a b : Fin m) (h1 h2 α hα) : unitDist G hG (.inner a b h1 h2 α hα) (.vtx c) =
    min (α + DD G a c) ((1 - α) + DD G b c) := by
  simp only [unitDist, rdist, dist_eq_sum G hG, DD, unitTree_w, mul_one]

lemma ud_ii (a b c d : Fin m) (h1 h2 α hα h3 h4 β hβ) :
    unitDist G hG (.inner a b h1 h2 α hα) (.inner c d h3 h4 β hβ) =
    if a = c ∧ b = d then |α - β| else min
        (min (α + DD G a c + β) (α + DD G a d + (1 - β)))
        (min ((1 - α) + DD G b c + β) ((1 - α) + DD G b d + (1 - β))) := by
  simp only [unitDist, rdist, dist_eq_sum G hG, DD, unitTree_w, mul_one]

/-- Coordinates of a point of `R(G)`: one coordinate per edge. -/
noncomputable def cr : RPoint G → Fin m × Fin m → ℝ
  | .vtx v, e => sd G e v
  | .inner a b _ _ α _, e => if e = (a, b) then α else sd G e a

lemma mem_Es_of {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) : (a, b) ∈ Es G :=
  (mem_Es G).mpr ⟨h2, h1⟩

include hG in
lemma sd_snd_eq {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) {e : Fin m × Fin m} (he : e ∈ Es G)
    (hne : e ≠ (a, b)) : sd G e b = sd G e a :=
  (sd_adj G hG he h1 (pair_ne_of_ne G he (mem_Es_of G h1 h2) (Ne.symm hne))).symm

lemma sum_split {e0 : Fin m × Fin m} (h0 : e0 ∈ Es G) (f : Fin m × Fin m → ℝ) :
    ∑ e ∈ Es G, f e = f e0 + ∑ e ∈ (Es G).erase e0, f e :=
  (Finset.add_sum_erase _ _ h0).symm

lemma sum_split2 {e0 e1 : Fin m × Fin m} (h0 : e0 ∈ Es G) (h1 : e1 ∈ Es G) (hne : e1 ≠ e0)
    (f : Fin m × Fin m → ℝ) :
    ∑ e ∈ Es G, f e = f e0 + f e1 + ∑ e ∈ ((Es G).erase e0).erase e1, f e := by
  rw [sum_split G h0, ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨hne, h1⟩), add_assoc]

lemma sd_fst' (a b : Fin m) : sd G (a, b) a = 0 := sd_fst G

include hG in
lemma sd_snd' {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) : sd G (a, b) b = 1 :=
  sd_snd G hG (mem_Es_of G h1 h2)

lemma cr_inner_self (a b : Fin m) (h1 h2 α hα) :
    cr G (.inner a b h1 h2 α hα) (a, b) = α := by simp [cr]

lemma cr_inner_ne (a b : Fin m) (h1 h2 α hα) {e : Fin m × Fin m} (hne : e ≠ (a, b)) :
    cr G (.inner a b h1 h2 α hα) e = sd G e a := by simp [cr, hne]

lemma cr_vtx (v : Fin m) (e : Fin m × Fin m) : cr G (.vtx v) e = sd G e v := rfl

include hG in
lemma vi_formula (c a b : Fin m) (h1 h2 α hα) :
    min (α + DD G a c) ((1 - α) + DD G b c) =
      ∑ e ∈ Es G, |cr G (.vtx c) e - cr G (.inner a b h1 h2 α hα) e| := by
  have h0 := mem_Es_of G h1 h2
  have hac : DD G a c = |0 - sd G (a, b) c| + ∑ e ∈ (Es G).erase (a, b), |sd G e a - sd G e c| := by
    unfold DD; rw [sum_split G h0, sd_fst']
  have hbc : DD G b c = |1 - sd G (a, b) c| + ∑ e ∈ (Es G).erase (a, b), |sd G e a - sd G e c| := by
    unfold DD; rw [sum_split G h0, sd_snd' G hG h1 h2]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [sd_snd_eq G hG h1 h2 (Finset.mem_of_mem_erase he) (Finset.ne_of_mem_erase he)]
  have hR : ∑ e ∈ Es G, |cr G (.vtx c) e - cr G (.inner a b h1 h2 α hα) e| =
      |sd G (a, b) c - α| + ∑ e ∈ (Es G).erase (a, b), |sd G e a - sd G e c| := by
    rw [sum_split G h0, cr_vtx, cr_inner_self]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [cr_vtx, cr_inner_ne G a b h1 h2 α hα (Finset.ne_of_mem_erase he), abs_sub_comm]
  rw [hac, hbc, hR]
  exact arith1 _ _ _ hα (sd_01 G _ _)

include hG in
lemma ii_formula (a b c d : Fin m) (h1 h2 α hα h3 h4 β hβ) (hne : ¬ (a = c ∧ b = d)) :
    min (min (α + DD G a c + β) (α + DD G a d + (1 - β)))
        (min ((1 - α) + DD G b c + β) ((1 - α) + DD G b d + (1 - β))) =
      ∑ e ∈ Es G, |cr G (.inner a b h1 h2 α hα) e - cr G (.inner c d h3 h4 β hβ) e| := by
  have h0 := mem_Es_of G h1 h2
  have h1' := mem_Es_of G h3 h4
  have hne' : (c, d) ≠ (a, b) := fun h => hne ⟨(Prod.ext_iff.mp h).1.symm, (Prod.ext_iff.mp h).2.symm⟩
  set R := ((Es G).erase (a, b)).erase (c, d)
  have hR1 : ∀ e ∈ R, e ≠ (a, b) := fun e he => Finset.ne_of_mem_erase (Finset.mem_of_mem_erase he)
  have hR2 : ∀ e ∈ R, e ≠ (c, d) := fun e he => Finset.ne_of_mem_erase he
  have hR3 : ∀ e ∈ R, e ∈ Es G := fun e he => Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he)
  have hd0 : sd G (a, b) d = sd G (a, b) c := sd_snd_eq G hG h3 h4 h0 hne'.symm
  have hb1 : sd G (c, d) b = sd G (c, d) a := sd_snd_eq G hG h1 h2 h1' hne'
  set S := ∑ e ∈ R, |sd G e a - sd G e c|
  have hac : DD G a c = |0 - sd G (a, b) c| + |sd G (c, d) a - 0| + S := by
    unfold DD; rw [sum_split2 G h0 h1' hne', sd_fst', sd_fst']
  have had : DD G a d = |0 - sd G (a, b) c| + |sd G (c, d) a - 1| + S := by
    unfold DD; rw [sum_split2 G h0 h1' hne', sd_fst', sd_snd' G hG h3 h4, hd0]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [sd_snd_eq G hG h3 h4 (hR3 e he) (hR2 e he)]
  have hbc : DD G b c = |1 - sd G (a, b) c| + |sd G (c, d) a - 0| + S := by
    unfold DD; rw [sum_split2 G h0 h1' hne', sd_snd' G hG h1 h2, sd_fst', hb1]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [sd_snd_eq G hG h1 h2 (hR3 e he) (hR1 e he)]
  have hbd : DD G b d = |1 - sd G (a, b) c| + |sd G (c, d) a - 1| + S := by
    unfold DD; rw [sum_split2 G h0 h1' hne', sd_snd' G hG h1 h2, sd_snd' G hG h3 h4, hb1, hd0]
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [sd_snd_eq G hG h1 h2 (hR3 e he) (hR1 e he), sd_snd_eq G hG h3 h4 (hR3 e he) (hR2 e he)]
  have hR : ∑ e ∈ Es G, |cr G (.inner a b h1 h2 α hα) e - cr G (.inner c d h3 h4 β hβ) e| =
      |α - sd G (a, b) c| + |sd G (c, d) a - β| + S := by
    rw [sum_split2 G h0 h1' hne', cr_inner_self, cr_inner_self, cr_inner_ne G c d h3 h4 β hβ hne'.symm,
      cr_inner_ne G a b h1 h2 α hα hne']
    congr 1
    refine Finset.sum_congr rfl fun e he => ?_
    rw [cr_inner_ne G a b h1 h2 α hα (hR1 e he), cr_inner_ne G c d h3 h4 β hβ (hR2 e he)]
  rw [hac, had, hbc, hbd, hR]
  exact arith2 _ _ _ _ _ hα hβ (sd_01 G _ _) (sd_01 G _ _)

include hG in
/-- **The coordinate formula**: `unitDist` is the `ℓ¹` distance of the edge coordinates. -/
theorem ud_eq (p q : RPoint G) : unitDist G hG p q = ∑ e ∈ Es G, |cr G p e - cr G q e| := by
  cases p with
  | vtx u =>
    cases q with
    | vtx v => rw [ud_vv]; rfl
    | inner a b h1 h2 α hα => rw [ud_vi, vi_formula G hG]
  | inner a b h1 h2 α hα =>
    cases q with
    | vtx c =>
      rw [ud_iv, vi_formula G hG c a b h1 h2 α hα]
      exact Finset.sum_congr rfl fun e _ => abs_sub_comm _ _
    | inner c d h3 h4 β hβ =>
      rw [ud_ii]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [sum_split G (mem_Es_of G h1 h2), cr_inner_self, cr_inner_self]
        have : ∑ e ∈ (Es G).erase (a, b),
            |cr G (.inner a b h1 h2 α hα) e - cr G (.inner a b h3 h4 β hβ) e| = 0 := by
          refine Finset.sum_eq_zero fun e he => ?_
          rw [cr_inner_ne G a b h1 h2 α hα (Finset.ne_of_mem_erase he),
            cr_inner_ne G a b h3 h4 β hβ (Finset.ne_of_mem_erase he), sub_self, abs_zero]
        rw [this, add_zero]
      · exact ii_formula G hG a b c d h1 h2 α hα h3 h4 β hβ h

/-- `r` lies on the geodesic `[p, q]`, in coordinates. -/
def InSeg (p q r : RPoint G) : Prop := ∀ e ∈ Es G, Bt (cr G p e) (cr G q e) (cr G r e)

include hG in
theorem seg_iff (p q r : RPoint G) : r ∈ seg G hG p q ↔ InSeg G p q r := by
  show unitDist G hG p r + unitDist G hG r q = unitDist G hG p q ↔ _
  rw [ud_eq G hG, ud_eq G hG, ud_eq G hG, ← Finset.sum_add_distrib, eq_comm,
    Finset.sum_eq_sum_iff_of_le (fun e _ => abs_sub_le _ _ _)]
  exact ⟨fun h e he => (h e he).symm, fun h e he => (h e he).symm⟩

/-- `x` is a median of `p, q, r`. -/
def IsMed (p q r x : RPoint G) : Prop := InSeg G p q x ∧ InSeg G q r x ∧ InSeg G p r x

lemma inseg_left (p q : RPoint G) : InSeg G p q p := fun _ _ => btw_left _ _
lemma inseg_right (p q : RPoint G) : InSeg G p q q := fun _ _ => btw_right _ _
lemma inseg_symm {p q r : RPoint G} (h : InSeg G p q r) : InSeg G q p r :=
  fun e he => btw_symm (h e he)

lemma med_swap12 {p q r x : RPoint G} (h : IsMed G p q r x) : IsMed G q p r x :=
  ⟨inseg_symm G h.1, h.2.2, h.2.1⟩
lemma med_swap23 {p q r x : RPoint G} (h : IsMed G p q r x) : IsMed G p r q x :=
  ⟨h.2.2, inseg_symm G h.2.1, h.1⟩

lemma med_reduce {p q r y x : RPoint G} (h1 : InSeg G p q y) (h2 : InSeg G p r y)
    (h : IsMed G y q r x) : IsMed G p q r x :=
  ⟨fun e he => btw_trans (h1 e he) (h.1 e he), h.2.1,
    fun e he => btw_trans (h2 e he) (h.2.2 e he)⟩

lemma inseg_conv {a b p q r : RPoint G} (h1 : InSeg G a b p) (h2 : InSeg G q r a)
    (h3 : InSeg G q r b) : InSeg G q r p :=
  fun e he => btw_conv (h1 e he) (h2 e he) (h3 e he)

lemma inseg_lift {c d q r t : RPoint G} (h1 : InSeg G c d q) (h2 : InSeg G c r t)
    (h3 : InSeg G d r t) : InSeg G q r t :=
  fun e he => btw_lift (h1 e he) (h2 e he) (h3 e he)

/-! ### Vertex medians -/

include hG in
lemma improve {u v w x : Fin m} (_hx : InSeg G (.vtx u) (.vtx v) (.vtx x)) {e0 : Fin m × Fin m}
    (h0 : e0 ∈ Es G) (hwx : sd G e0 w ≠ sd G e0 x) (huv : sd G e0 u ≠ sd G e0 v) :
    ∃ y, InSeg G (.vtx u) (.vtx v) (.vtx y) ∧ DD G w y < DD G w x := by
  classical
  let y := if sd G e0 w = 0 then e0.1 else e0.2
  have hy0 : sd G e0 y = sd G e0 w := by
    rcases sd_01 G e0 w with h | h
    · simp only [y, h, if_true]; exact sd_fst G
    · simp only [y, h, if_neg one_ne_zero]; exact sd_snd G hG h0
  have hy : ∀ e ∈ Es G, ∀ z : Fin m, sd G e e0.1 = sd G e z → sd G e e0.2 = sd G e z →
      sd G e y = sd G e z := by
    intro e _ z h1 h2
    by_cases h : sd G e0 w = 0
    · simp only [y, h, if_true]; exact h1
    · simp only [y, h, if_false]; exact h2
  refine ⟨y, ?_, ?_⟩
  · intro e he
    rw [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)]
    rintro ⟨h1, h2⟩
    obtain ⟨k1, k2⟩ := sep G hG he h0 h1 huv
    exact h2 (hy e he u k1 k2)
  · apply Finset.sum_lt_sum
    · intro e he
      by_cases h : sd G e w = sd G e x
      · obtain ⟨k1, k2⟩ := sep G hG he h0 h hwx
        rw [hy e he w k1 k2, sub_self, abs_zero]; exact abs_nonneg _
      · rw [abs_sd_sub G e w x, if_neg h, abs_sd_sub]; split_ifs <;> norm_num
    · refine ⟨e0, h0, ?_⟩
      rw [hy0, sub_self, abs_zero, abs_sd_sub, if_neg hwx]; norm_num

include hG in
theorem vmed (u v w : Fin m) : ∃ x, IsMed G (.vtx u) (.vtx v) (.vtx w) (.vtx x) := by
  classical
  let M := Finset.univ.filter (fun x : Fin m => InSeg G (.vtx u) (.vtx v) (.vtx x))
  have huM : u ∈ M := by simp [M, inseg_left]
  obtain ⟨x, hxM, hmin⟩ := M.exists_min_image (fun x => DD G w x) ⟨u, huM⟩
  have hx : InSeg G (.vtx u) (.vtx v) (.vtx x) := (Finset.mem_filter.mp hxM).2
  have key : ∀ e0 ∈ Es G, sd G e0 w ≠ sd G e0 x → sd G e0 u ≠ sd G e0 v → False := by
    intro e0 h0 h1 h2
    obtain ⟨y, hy, hlt⟩ := improve G hG hx h0 h1 h2
    exact absurd (hmin y (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)) (not_le.mpr hlt)
  have hxe : ∀ e ∈ Es G, ¬ (sd G e u = sd G e v ∧ sd G e x ≠ sd G e u) := by
    intro e he
    have := hx e he
    rwa [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)] at this
  refine ⟨x, ?_, ?_, ?_⟩
  · exact hx
  · intro e he
    rw [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)]
    rintro ⟨h1, h2⟩
    refine key e he (by rw [← h1]; exact Ne.symm h2) (fun h3 => hxe e he ⟨h3, ?_⟩)
    rw [h3]; exact h2
  · intro e he
    rw [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)]
    rintro ⟨h1, h2⟩
    exact key e he (by rw [← h1]; exact Ne.symm h2) (fun h3 => hxe e he ⟨h3, h2⟩)

/-! ### Medians of arbitrary points -/

/-- `q` lies on the closed edge `[a, b]`: all its coordinates away from `(a, b)` are those of `a`. -/
def OnEdge (a b : Fin m) (q : RPoint G) : Prop := ∀ e ∈ Es G, e ≠ (a, b) → cr G q e = sd G e a

lemma onEdge_inner (a b : Fin m) (h1 h2 α hα) : OnEdge G a b (.inner a b h1 h2 α hα) :=
  fun _ _ hne => cr_inner_ne G a b h1 h2 α hα hne

lemma onEdge_a (a b : Fin m) : OnEdge G a b (.vtx a) := fun _ _ _ => rfl

include hG in
lemma onEdge_b {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) : OnEdge G a b (.vtx b) :=
  fun _ he hne => sd_snd_eq G hG h1 h2 he hne

lemma line {a b : Fin m} {p q r : RPoint G} (hp : OnEdge G a b p) (hq : OnEdge G a b q)
    (hr : OnEdge G a b r) : ∃ x, IsMed G p q r x := by
  have hoff : ∀ e ∈ Es G, e ≠ (a, b) → ∀ x y z : RPoint G, OnEdge G a b x → OnEdge G a b y →
      OnEdge G a b z → Bt (cr G x e) (cr G y e) (cr G z e) := by
    intro e he hne x y z hx hy hz
    rw [hx e he hne, hy e he hne, hz e he hne]; exact btw_self _
  have mk : ∀ x, OnEdge G a b x → Bt (cr G p (a, b)) (cr G q (a, b)) (cr G x (a, b)) →
      Bt (cr G q (a, b)) (cr G r (a, b)) (cr G x (a, b)) →
      Bt (cr G p (a, b)) (cr G r (a, b)) (cr G x (a, b)) → IsMed G p q r x := by
    intro x hx k1 k2 k3
    refine ⟨fun e he => ?_, fun e he => ?_, fun e he => ?_⟩ <;>
    · by_cases hne : e = (a, b)
      · subst hne; assumption
      · exact hoff e he hne _ _ _ (by assumption) (by assumption) hx
  rcases btw_med3 (cr G p (a, b)) (cr G q (a, b)) (cr G r (a, b)) with
    ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩ | ⟨k1, k2, k3⟩
  · exact ⟨p, mk p hp k1 k2 k3⟩
  · exact ⟨q, mk q hq k1 k2 k3⟩
  · exact ⟨r, mk r hr k1 k2 k3⟩

lemma classify (a b : Fin m) (q : RPoint G) :
    OnEdge G a b q ∨ cr G q (a, b) = 0 ∨ cr G q (a, b) = 1 := by
  cases q with
  | vtx v => exact Or.inr (sd_01 G _ _)
  | inner c d h3 h4 β hβ =>
    by_cases h : (a, b) = (c, d)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact Or.inl (onEdge_inner G a b h3 h4 β hβ)
    · right; rw [cr_inner_ne G c d h3 h4 β hβ h]; exact sd_01 G _ _

lemma toA {a b : Fin m} {p r : RPoint G} (hp : OnEdge G a b p) (hr : cr G r (a, b) = 0) :
    InSeg G p r (.vtx a) := by
  intro e he
  by_cases hne : e = (a, b)
  · subst hne; rw [cr_vtx, hr, sd_fst']; exact btw_right _ _
  · rw [cr_vtx, hp e he hne]; exact btw_left _ _

include hG in
lemma toB {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) {p r : RPoint G} (hp : OnEdge G a b p)
    (hr : cr G r (a, b) = 1) : InSeg G p r (.vtx b) := by
  intro e he
  by_cases hne : e = (a, b)
  · subst hne; rw [cr_vtx, hr, sd_snd' G hG h1 h2]; exact btw_right _ _
  · rw [cr_vtx, hp e he hne, sd_snd_eq G hG h1 h2 he hne]; exact btw_left _ _

include hG in
lemma ab_inner (a b : Fin m) (h1 h2 α hα) : InSeg G (.vtx a) (.vtx b) (.inner a b h1 h2 α hα) := by
  intro e he
  by_cases hne : e = (a, b)
  · subst hne
    rw [cr_vtx, cr_vtx, cr_inner_self, sd_fst', sd_snd' G hG h1 h2, btw_iff]
    exact Or.inl ⟨hα.1.le, hα.2.le⟩
  · rw [cr_vtx, cr_vtx, cr_inner_ne G a b h1 h2 α hα hne, sd_snd_eq G hG h1 h2 he hne]
    exact btw_self _

include hG in
lemma ends (q : RPoint G) : ∃ c d : Fin m, InSeg G (.vtx c) (.vtx d) q ∧
    ∀ e ∈ Es G, (cr G q e = 0 ∨ cr G q e = 1) → sd G e c = cr G q e ∧ sd G e d = cr G q e := by
  cases q with
  | vtx v => exact ⟨v, v, inseg_left G _ _, fun _ _ _ => ⟨rfl, rfl⟩⟩
  | inner c d h3 h4 β hβ =>
    refine ⟨c, d, ab_inner G hG c d h3 h4 β hβ, fun e he h01 => ?_⟩
    by_cases hne : e = (c, d)
    · subst hne; rw [cr_inner_self] at h01
      rcases h01 with h | h <;> linarith [hβ.1, hβ.2]
    · rw [cr_inner_ne G c d h3 h4 β hβ hne, sd_snd_eq G hG h3 h4 he hne]; exact ⟨rfl, rfl⟩

include hG in
lemma vsep {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) {u v : Fin m} (hu : sd G (a, b) u = 0)
    (hv : sd G (a, b) v = 1) :
    InSeg G (.vtx u) (.vtx v) (.vtx a) ∧ InSeg G (.vtx u) (.vtx v) (.vtx b) := by
  have h0 := mem_Es_of G h1 h2
  have huv : sd G (a, b) u ≠ sd G (a, b) v := by rw [hu, hv]; norm_num
  constructor <;>
  · intro e he
    rw [cr_vtx, cr_vtx, cr_vtx, btw_01 (sd_01 G _ _) (sd_01 G _ _) (sd_01 G _ _)]
    rintro ⟨k1, k2⟩
    obtain ⟨k3, k4⟩ := sep G hG he h0 k1 huv
    exact k2 (by assumption)

include hG in
lemma gsep {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) {q r : RPoint G} (hq : cr G q (a, b) = 0)
    (hr : cr G r (a, b) = 1) : InSeg G q r (.vtx a) ∧ InSeg G q r (.vtx b) := by
  have h0 := mem_Es_of G h1 h2
  obtain ⟨c1, d1, hq1, hq2⟩ := ends G hG q
  obtain ⟨c2, d2, hr1, hr2⟩ := ends G hG r
  obtain ⟨k1, k2⟩ := hq2 _ h0 (Or.inl hq)
  obtain ⟨k3, k4⟩ := hr2 _ h0 (Or.inr hr)
  rw [hq] at k1 k2; rw [hr] at k3 k4
  have hc := vsep G hG h1 h2 k1 k3
  have hd := vsep G hG h1 h2 k1 k4
  have hc' := vsep G hG h1 h2 k2 k3
  have hd' := vsep G hG h1 h2 k2 k4
  have L : ∀ t : RPoint G, InSeg G (.vtx c1) (.vtx c2) t → InSeg G (.vtx c1) (.vtx d2) t →
      InSeg G (.vtx d1) (.vtx c2) t → InSeg G (.vtx d1) (.vtx d2) t → InSeg G q r t := by
    intro t t1 t2 t3 t4
    apply inseg_lift G hq1
    · exact inseg_symm G (inseg_lift G hr1 (inseg_symm G t1) (inseg_symm G t2))
    · exact inseg_symm G (inseg_lift G hr1 (inseg_symm G t3) (inseg_symm G t4))
  exact ⟨L _ hc.1 hd.1 hc'.1 hd'.1, L _ hc.2 hd.2 hc'.2 hd'.2⟩

lemma core_onEdge {a b : Fin m} {p q r : RPoint G} (t : Fin m) (ht : OnEdge G a b (.vtx t))
    (hto : ∀ p', OnEdge G a b p' → InSeg G p' r (.vtx t)) (hp : OnEdge G a b p)
    (hq : OnEdge G a b q) : ∃ x, IsMed G p q r x := by
  obtain ⟨x, hx⟩ := line G hp hq ht
  refine ⟨x, med_swap23 G (med_swap12 G ?_)⟩
  exact med_reduce G (inseg_symm G (hto p hp)) (inseg_symm G (hto q hq))
    (med_swap12 G (med_swap23 G hx))

include hG in
lemma core {a b : Fin m} (h1 : G.Adj a b) (h2 : a < b) (α : ℝ) (hα : 0 < α ∧ α < 1)
    (q r : RPoint G) (hA : ∃ x, IsMed G (.vtx a) q r x) (hB : ∃ x, IsMed G (.vtx b) q r x) :
    ∃ x, IsMed G (.inner a b h1 h2 α hα) q r x := by
  set p : RPoint G := .inner a b h1 h2 α hα
  have hp := onEdge_inner G a b h1 h2 α hα
  have hA' := onEdge_a G a b
  have hB' := onEdge_b G hG h1 h2
  have mid : ∀ q r : RPoint G, cr G q (a, b) = 0 → cr G r (a, b) = 1 → IsMed G p q r p := by
    intro q r hq hr
    obtain ⟨k1, k2⟩ := gsep G hG h1 h2 hq hr
    exact ⟨inseg_left G _ _, inseg_conv G (ab_inner G hG a b h1 h2 α hα) k1 k2, inseg_left G _ _⟩
  rcases classify G a b q with hq | hq | hq <;> rcases classify G a b r with hr | hr | hr
  · exact line G hp hq hr
  · exact core_onEdge G a hA' (fun p' hp' => toA G hp' hr) hp hq
  · exact core_onEdge G b hB' (fun p' hp' => toB G hG h1 h2 hp' hr) hp hq
  · obtain ⟨x, hx⟩ := core_onEdge G a hA' (fun p' hp' => toA G hp' hq) hp hr
    exact ⟨x, med_swap23 G hx⟩
  · obtain ⟨x, hx⟩ := hA
    exact ⟨x, med_reduce G (toA G hp hq) (toA G hp hr) hx⟩
  · exact ⟨p, mid q r hq hr⟩
  · obtain ⟨x, hx⟩ := core_onEdge G b hB' (fun p' hp' => toB G hG h1 h2 hp' hq) hp hr
    exact ⟨x, med_swap23 G hx⟩
  · exact ⟨p, med_swap23 G (mid r q hr hq)⟩
  · obtain ⟨x, hx⟩ := hB
    exact ⟨x, med_reduce G (toB G hG h1 h2 hp hq) (toB G hG h1 h2 hp hr) hx⟩

/-- Number of interior points. -/
def nI : RPoint G → ℕ
  | .vtx _ => 0
  | .inner .. => 1

include hG in
lemma med_aux : ∀ n : ℕ, ∀ p q r : RPoint G, nI G p + nI G q + nI G r ≤ n →
    ∃ x, IsMed G p q r x := by
  intro n
  induction n with
  | zero =>
    intro p q r h
    cases p with
    | inner => simp [nI] at h
    | vtx u =>
      cases q with
      | inner => simp [nI] at h
      | vtx v =>
        cases r with
        | inner => simp [nI] at h
        | vtx w => obtain ⟨x, hx⟩ := vmed G hG u v w; exact ⟨_, hx⟩
  | succ n ih =>
    intro p q r h
    cases p with
    | inner a b h1 h2 α hα =>
      exact core G hG h1 h2 α hα q r (ih _ _ _ (by simp [nI] at h ⊢; omega))
        (ih _ _ _ (by simp [nI] at h ⊢; omega))
    | vtx u =>
      cases q with
      | inner a b h1 h2 α hα =>
        obtain ⟨x, hx⟩ := core G hG h1 h2 α hα (.vtx u) r (ih _ _ _ (by simp [nI] at h ⊢; omega))
          (ih _ _ _ (by simp [nI] at h ⊢; omega))
        exact ⟨x, med_swap12 G hx⟩
      | vtx v =>
        cases r with
        | inner a b h1 h2 α hα =>
          obtain ⟨x, hx⟩ := core G hG h1 h2 α hα (.vtx u) (.vtx v)
            (ih _ _ _ (by simp [nI])) (ih _ _ _ (by simp [nI]))
          exact ⟨x, med_swap23 G (med_swap12 G hx)⟩
        | vtx w => obtain ⟨x, hx⟩ := vmed G hG u v w; exact ⟨_, hx⟩

include hG in
/-- **Medians in `R(G)`**: any three points have a point on all three pairwise geodesics. -/
theorem exists_median (a b c : RPoint G) :
    ∃ x, x ∈ seg G hG a b ∧ x ∈ seg G hG b c ∧ x ∈ seg G hG a c := by
  obtain ⟨x, h1, h2, h3⟩ := med_aux G hG 3 a b c (by cases a <;> cases b <;> cases c <;> simp [nI])
  exact ⟨x, (seg_iff G hG _ _ _).mpr h1, (seg_iff G hG _ _ _).mpr h2, (seg_iff G hG _ _ _).mpr h3⟩

/-! ### Helly property -/

/-- Geodesic convexity. -/
def Cvx (S : Set (RPoint G)) : Prop := ∀ p ∈ S, ∀ q ∈ S, seg G hG p q ⊆ S

lemma helly3 {A B C : Set (RPoint G)} (hA : Cvx G hG A) (hB : Cvx G hG B) (hC : Cvx G hG C)
    (hAB : (A ∩ B).Nonempty) (hBC : (B ∩ C).Nonempty) (hAC : (A ∩ C).Nonempty) :
    ∃ p, p ∈ A ∧ p ∈ B ∧ p ∈ C := by
  obtain ⟨a, haB, haC⟩ := hBC
  obtain ⟨b, hbA, hbC⟩ := hAC
  obtain ⟨c, hcA, hcB⟩ := hAB
  obtain ⟨x, h1, h2, h3⟩ := exists_median G hG a b c
  exact ⟨x, hA b hbA c hcA h2, hB a haB c hcB h3, hC a haC b hbC h1⟩

lemma hellyN : ∀ k : ℕ, ∀ X : Fin (k + 1) → Set (RPoint G), (∀ i, Cvx G hG (X i)) →
    (∀ i j, (X i ∩ X j).Nonempty) → ∃ p, ∀ i, p ∈ X i := by
  intro k
  induction k with
  | zero =>
    intro X _ hint
    obtain ⟨p, hp, _⟩ := hint 0 0
    exact ⟨p, fun i => by rw [Fin.fin_one_eq_zero i]; exact hp⟩
  | succ k ih =>
    intro X hX hint
    let Y : Fin (k + 1) → Set (RPoint G) := fun i => X i.castSucc ∩ X (Fin.last (k + 1))
    have hY : ∀ i, Cvx G hG (Y i) := fun i p hp q hq =>
      Set.subset_inter (hX _ p hp.1 q hq.1) (hX _ p hp.2 q hq.2)
    have hYint : ∀ i j, (Y i ∩ Y j).Nonempty := by
      intro i j
      obtain ⟨p, h1, h2, h3⟩ := helly3 G hG (hX i.castSucc) (hX j.castSucc) (hX (Fin.last _))
        (hint _ _) (hint _ _) (hint _ _)
      exact ⟨p, ⟨h1, h3⟩, ⟨h2, h3⟩⟩
    obtain ⟨p, hp⟩ := ih Y hY hYint
    refine ⟨p, fun i => ?_⟩
    induction i using Fin.lastCases with
    | last => exact (hp 0).2
    | cast i => exact (hp i).1

end Sides
end MTSPHelly

open MetricTSPSublinear in
theorem solution {m : ℕ} (G : SimpleGraph (Fin m)) (hG : G.IsTree) (k : ℕ) (X : Fin k → Set (RPoint G))
    (hX : ∀ i, IsSubtree G hG (X i)) (hint : ∀ i j, (X i ∩ X j).Nonempty) :
    ∃ p : RPoint G, ∀ i, p ∈ X i := by
  cases k with
  | zero =>
    obtain ⟨v⟩ := hG.connected.nonempty
    exact ⟨.vtx v, fun i => i.elim0⟩
  | succ k => exact MTSPHelly.hellyN G hG k X (fun i => (hX i).2.1) hint
