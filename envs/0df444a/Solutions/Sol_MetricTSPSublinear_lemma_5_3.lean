-- Prove2me | solution 1 for MetricTSPSublinear.lemma_5_3
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-26T23:23:40.222742+00:00
-- url     : https://prove2.me/submissions/d1291e94-6a8e-45c2-ad4d-ec774ff7001d

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_Dominated
import Definitions.Def_MetricTSPSublinear_rdist


namespace MTSPTree
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

lemma reach_or_reach_aux {a b : V} : ∀ (w t : V) (p : G.Walk w t), t = a →
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

/-- After deleting a tree edge `{a,b}`, every vertex is still connected to `a` or to `b`. -/
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

/-- Reachability classes after deleting an edge of a tree. -/
lemma reach_iff_reach (hT : G.IsTree) {a b : V} (hadj : G.Adj a b) (x p q : V) :
    ((G.deleteEdges {s(a, b)}).Reachable x p ↔ (G.deleteEdges {s(a, b)}).Reachable x q) ↔
      (G.deleteEdges {s(a, b)}).Reachable p q := by
  set R := (G.deleteEdges {s(a, b)}).Reachable with hRdef
  have hab : ¬ R a b := not_reach_of_adj hT.isAcyclic hadj
  have hx := reach_or_reach hT.connected (a := a) (b := b) x
  have hp := reach_or_reach hT.connected (a := a) (b := b) p
  have hq := reach_or_reach hT.connected (a := a) (b := b) q
  constructor
  · intro h
    by_cases hxp : R x p
    · exact hxp.symm.trans (h.mp hxp)
    · have hxq : ¬ R x q := fun hh => hxp (h.mpr hh)
      rcases hx with hx | hx
      · have hpb : R p b := by
          rcases hp with hp | hp
          · exact absurd (hx.trans hp.symm) hxp
          · exact hp
        have hqb : R q b := by
          rcases hq with hq | hq
          · exact absurd (hx.trans hq.symm) hxq
          · exact hq
        exact hpb.trans hqb.symm
      · have hpa : R p a := by
          rcases hp with hp | hp
          · exact hp
          · exact absurd (hx.trans hp.symm) hxp
        have hqa : R q a := by
          rcases hq with hq | hq
          · exact hq
          · exact absurd (hx.trans hq.symm) hxq
        exact hpa.trans hqa.symm
  · intro h
    exact ⟨fun h1 => h1.trans h, fun h1 => h1.trans h.symm⟩

/-- In a finite tree, behind every edge `a → b` (on the side of `b`) there is a vertex of degree
at most one. -/
lemma exists_leaf_behind [Fintype V] [DecidableEq V] (hT : G.IsTree) {a b : V} (hadj : G.Adj a b) :
    ∃ c, (G.deleteEdges {s(a, b)}).Reachable b c ∧ ∀ y₁ y₂, G.Adj c y₁ → G.Adj c y₂ → y₁ = y₂ := by
  classical
  let s : Set ℕ := {k | ∃ (c : V) (q : G.Walk b c), q.IsPath ∧ a ∉ q.support ∧ q.length = k}
  have hfin : s.Finite := Set.Finite.subset (Set.finite_le_nat (Fintype.card V))
    (fun k ⟨_, q, hq, _, hk⟩ => hk ▸ le_of_lt hq.length_lt)
  have hb0 : (0 : ℕ) ∈ s := ⟨b, Walk.nil, Walk.IsPath.nil, by
    simp only [Walk.support_nil, List.mem_singleton]; exact hadj.ne, rfl⟩
  obtain ⟨k, ⟨c, q, hq, haq, hk⟩, hmax⟩ := hfin.exists_maximal ⟨0, hb0⟩
  have hext : ∀ y, G.Adj c y → y ∉ q.support → y ≠ a → False := by
    intro y hcy hy hya
    have hq2 : (q.concat hcy).IsPath := hq.concat hy hcy
    have hmem : (q.concat hcy).length ∈ s := ⟨y, q.concat hcy, hq2, by
      simp only [Walk.support_concat, List.concat_eq_append, List.mem_append, List.mem_singleton,
        not_or]
      exact ⟨haq, fun h => hya h.symm⟩, rfl⟩
    have := hmax hmem (by rw [Walk.length_concat, hk]; omega)
    rw [Walk.length_concat, hk] at this
    omega
  have hRq : (G.deleteEdges {s(a, b)}).Reachable b c := by
    refine ⟨q.toDeleteEdge (s(a, b)) ?_⟩
    intro hmem
    exact haq (q.fst_mem_support_of_mem_edges hmem)
  refine ⟨c, hRq, ?_⟩
  -- every neighbour of `c` is a fixed vertex
  have hnb : ∀ y, G.Adj c y → y = (if c = b then a else q.penultimate) := by
    intro y hcy
    by_cases hcb : c = b
    · subst hcb
      rw [if_pos rfl]
      have hqnil : q = Walk.nil := Walk.isPath_iff_eq_nil.mp hq
      by_contra hya
      apply hext y hcy _ hya
      rw [hqnil, Walk.support_nil, List.mem_singleton]
      exact hcy.ne.symm
    · rw [if_neg hcb]
      by_cases hy : y ∈ q.support
      · exact hT.isAcyclic.eq_penultimate_of_adj_end hq hcy hy
      · by_cases hya : y = a
        · exfalso
          subst hya
          -- two different paths from `y = a` to `c`
          have hP : (Walk.cons hadj q).IsPath := hq.cons haq
          have h1 : (⟨Walk.cons hadj q, hP⟩ : G.Path y c) = Path.singleton hcy.symm :=
            (hT.isAcyclic.subsingleton_path y c).elim _ _
          have hlen := congrArg (fun P : G.Path y c => P.val.length) h1
          simp only [Walk.length_cons, Path.singleton_coe, Walk.length_cons, Walk.length_nil] at hlen
          have : q.length = 0 := by omega
          exact hcb (Walk.eq_of_length_eq_zero this).symm
        · exact absurd (hext y hcy hy hya) id
  intro y₁ y₂ h1 h2
  rw [hnb y₁ h1, hnb y₂ h2]

end MTSPTree



/-! Infrastructure for Lemma 5.3: tree distances, points along root paths, distance bounds. -/

namespace Q53
open MetricTSPSublinear SimpleGraph

variable {m : ℕ} (T : TreeCoverLB.WeightedTree (Fin m))

/-- Weight of a walk. -/
noncomputable def L {a b : Fin m} (p : T.G.Walk a b) : ℝ :=
  KServer.walkWeight (fun u v => T.w s(u, v)) p

lemma L_nil (a : Fin m) : L T (Walk.nil : T.G.Walk a a) = 0 := by
  simp [L, KServer.walkWeight]

lemma L_cons {a b c : Fin m} (h : T.G.Adj a b) (p : T.G.Walk b c) :
    L T (Walk.cons h p) = T.w s(a, b) + L T p := by
  simp [L, KServer.walkWeight]

lemma L_append {a b c : Fin m} (p : T.G.Walk a b) (q : T.G.Walk b c) :
    L T (p.append q) = L T p + L T q := by
  simp [L, KServer.walkWeight, Walk.darts_append]

lemma L_reverse {a b : Fin m} (p : T.G.Walk a b) : L T p.reverse = L T p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [Walk.reverse_cons, L_append, ih, L_cons, L_cons, L_nil, Sym2.eq_swap]; ring

lemma L_nonneg {a b : Fin m} (p : T.G.Walk a b) : 0 ≤ L T p := by
  induction p with
  | nil => rw [L_nil]
  | cons h p ih => rw [L_cons]; exact add_nonneg (T.w_nonneg _ h) ih

lemma path_isPath (a b : Fin m) : (T.path a b).IsPath :=
  (T.isTree.existsUnique_path a b).exists.choose_spec

lemma dist_def (a b : Fin m) : T.dist a b = L T (T.path a b) := rfl

lemma dist_eq_L {a b : Fin m} (p : T.G.Walk a b) (hp : p.IsPath) : T.dist a b = L T p := by
  have := (T.isTree.existsUnique_path a b).unique (path_isPath T a b) hp
  rw [dist_def, this]

lemma dist_self (a : Fin m) : T.dist a a = 0 := by
  rw [dist_eq_L T Walk.nil Walk.IsPath.nil, L_nil]

lemma dist_comm (a b : Fin m) : T.dist a b = T.dist b a := by
  rw [dist_eq_L T _ (path_isPath T a b).reverse, L_reverse, dist_def]

lemma dist_adj {a b : Fin m} (h : T.G.Adj a b) : T.dist a b = T.w s(a, b) := by
  have hp : (Walk.cons h Walk.nil : T.G.Walk a b).IsPath :=
    (Walk.cons_isPath_iff _ _).mpr ⟨Walk.IsPath.nil, by simp [h.ne]⟩
  rw [dist_eq_L T _ hp, L_cons, L_nil, add_zero]

lemma dist_triangle (a b c : Fin m) : T.dist a c ≤ T.dist a b + T.dist b c := by
  let W := (T.path a b).append (T.path b c)
  rw [dist_eq_L T W.bypass W.bypass_isPath, dist_def T a b, dist_def T b c, ← L_append]
  unfold L KServer.walkWeight
  apply List.Sublist.sum_le_sum ((W.darts_bypass_sublist_darts).map _)
  intro x hx
  obtain ⟨dd, _, rfl⟩ := List.mem_map.mp hx
  exact T.w_nonneg _ dd.adj

lemma dist_nonneg (a b : Fin m) : 0 ≤ T.dist a b := by
  have := dist_triangle T a b a
  rw [dist_self, dist_comm T b a] at this
  linarith

lemma dist_split {x y z : Fin m} (hz : z ∈ (T.path x y).support) :
    T.dist x y = T.dist x z + T.dist z y := by
  have hp := path_isPath T x y
  rw [dist_eq_L T _ (hp.takeUntil hz), dist_eq_L T _ (hp.dropUntil hz), ← L_append,
    Walk.take_spec, dist_def]

/-- The bridge decomposition of distances across an edge. -/
lemma bridge {a a1 z y : Fin m} (h : T.G.Adj a a1)
    (hz : (T.G.deleteEdges {s(a, a1)}).Reachable z a)
    (hy : (T.G.deleteEdges {s(a, a1)}).Reachable a1 y) :
    T.dist z y = T.dist z a + T.w s(a, a1) + T.dist a1 y := by
  have hna : ¬ (T.G.deleteEdges {s(a, a1)}).Reachable a a1 :=
    MTSPTree.not_reach_of_adj T.isTree.isAcyclic h
  have h1 : s(a, a1) ∈ (T.path z y).edges := by
    rw [MTSPTree.mem_path_edges_iff T.isTree _ (path_isPath T z y)]
    intro hzy; exact hna (hz.symm.trans (hzy.trans hy.symm))
  have h2 : s(a, a1) ∈ (T.path a y).edges := by
    rw [MTSPTree.mem_path_edges_iff T.isTree _ (path_isPath T a y)]
    intro hay; exact hna (hay.trans hy.symm)
  rw [dist_split T ((T.path z y).fst_mem_support_of_mem_edges h1),
    dist_split T (z := a1) ((T.path a y).snd_mem_support_of_mem_edges h2), dist_adj T h]
  ring

lemma reach_cons {a a1 y : Fin m} (h : T.G.Adj a a1) (p : T.G.Walk a1 y)
    (hp : (Walk.cons h p).IsPath) : (T.G.deleteEdges {s(a, a1)}).Reachable a1 y :=
  ⟨p.toDeleteEdge _ (fun he => ((Walk.cons_isPath_iff h p).mp hp).2
    (p.fst_mem_support_of_mem_edges he))⟩

/-! ### Points of `R(T)` -/

/-- The point at fraction `β` from `a` on the edge `{a, b}`. -/
noncomputable def edgePt {a b : Fin m} (h : T.G.Adj a b) (β : ℝ) (hβ : 0 < β ∧ β < 1) :
    RPoint T.G :=
  if hlt : a < b then RPoint.inner a b h hlt β hβ
  else RPoint.inner b a h.symm (lt_of_le_of_ne (not_lt.mp hlt) h.ne.symm) (1 - β)
    ⟨by linarith [hβ.2], by linarith [hβ.1]⟩

lemma rdist_edgePt_vtx {a b : Fin m} (h : T.G.Adj a b) (β : ℝ) (hβ : 0 < β ∧ β < 1) (c : Fin m) :
    rdist T (edgePt T h β hβ) (RPoint.vtx c) =
      min (β * T.w s(a, b) + T.dist a c) ((1 - β) * T.w s(a, b) + T.dist b c) := by
  unfold edgePt
  split_ifs with hlt
  · simp only [rdist]
  · simp only [rdist]
    rw [Sym2.eq_swap, min_comm]
    congr 2; ring

lemma rdist_edgePt_same {a b : Fin m} (h : T.G.Adj a b) (β β' : ℝ) (hβ : 0 < β ∧ β < 1)
    (hβ' : 0 < β' ∧ β' < 1) :
    rdist T (edgePt T h β hβ) (edgePt T h β' hβ') = |β - β'| * T.w s(a, b) := by
  unfold edgePt
  split_ifs with hlt
  · simp only [rdist, and_self, if_true]
  · simp only [rdist, and_self, if_true]
    rw [Sym2.eq_swap]
    congr 1
    rw [show 1 - β - (1 - β') = -(β - β') by ring, abs_neg]

lemma rdist_comm (P Q : RPoint T.G) : rdist T P Q = rdist T Q P := by
  cases P with
  | vtx a =>
    cases Q with
    | vtx b => simp only [rdist]; exact dist_comm T a b
    | inner b e hbe hlt β hβ => simp only [rdist]
  | inner a b hab hlt α hα =>
    cases Q with
    | vtx c => simp only [rdist]
    | inner c e hce hlt' β hβ =>
      simp only [rdist]
      by_cases h : a = c ∧ b = e
      · obtain ⟨rfl, rfl⟩ := h
        simp [abs_sub_comm]
      · rw [if_neg h, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), min_min_min_comm
          (β * T.w s(c, e) + T.dist c a + α * T.w s(a, b))]
        rw [dist_comm T a c, dist_comm T a e, dist_comm T b c, dist_comm T b e]
        congr 2 <;> ring

lemma le_min_add_min {A B C D X : ℝ} (h1 : X ≤ A + C) (h2 : X ≤ A + D) (h3 : X ≤ B + C)
    (h4 : X ≤ B + D) : X ≤ min A B + min C D := by
  rcases le_total A B with h | h <;> rcases le_total C D with h' | h' <;>
    simp only [min_eq_left, min_eq_right, h, h'] <;> assumption

lemma min_le_add_min_left {A B C D X : ℝ} (h1 : A ≤ X + C) (h2 : B ≤ X + D) :
    min A B ≤ X + min C D := by
  rcases le_total C D with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans h1
  · rw [min_eq_right h]; exact (min_le_right _ _).trans h2

lemma min_le_add_min_right {A B C D X : ℝ} (h1 : A ≤ C + X) (h2 : B ≤ D + X) :
    min A B ≤ min C D + X := by
  rcases le_total C D with h | h
  · rw [min_eq_left h]; exact (min_le_left _ _).trans h1
  · rw [min_eq_right h]; exact (min_le_right _ _).trans h2

/-- Triangle inequality through a node. -/
lemma rdist_tri (P Q : RPoint T.G) (c : Fin m) :
    rdist T P Q ≤ rdist T P (RPoint.vtx c) + rdist T (RPoint.vtx c) Q := by
  cases P with
  | vtx a =>
    cases Q with
    | vtx b => simp only [rdist]; exact dist_triangle T a c b
    | inner b e hbe hlt β hβ =>
      simp only [rdist]
      apply min_le_add_min_left
      · linarith [dist_triangle T b c a, dist_comm T c a]
      · linarith [dist_triangle T e c a, dist_comm T c a]
  | inner a b hab hlt α hα =>
    cases Q with
    | vtx e =>
      simp only [rdist]
      apply min_le_add_min_right
      · linarith [dist_triangle T a c e]
      · linarith [dist_triangle T b c e]
    | inner c' e hce hlt' β hβ =>
      simp only [rdist]
      have hw := T.w_nonneg s(a, b) hab
      have hw' := T.w_nonneg s(c', e) hce
      by_cases h : a = c' ∧ b = e
      · obtain ⟨rfl, rfl⟩ := h
        rw [if_pos ⟨rfl, rfl⟩]
        have hab' := dist_adj T hab
        have t1 := dist_triangle T a c b
        have n1 := dist_nonneg T a c
        have n2 := dist_nonneg T b c
        have dc := dist_comm T c b
        have p1 := mul_nonneg hα.1.le hw
        have p2 := mul_nonneg hβ.1.le hw
        have p3 := mul_nonneg (sub_nonneg.mpr hα.2.le) hw
        have p4 := mul_nonneg (sub_nonneg.mpr hβ.2.le) hw
        rcases abs_cases (α - β) with ⟨habs, _⟩ | ⟨habs, _⟩ <;> rw [habs] <;>
          apply le_min_add_min <;> nlinarith
      · rw [if_neg h]
        have t1 := dist_triangle T a c c'
        have t2 := dist_triangle T a c e
        have t3 := dist_triangle T b c c'
        have t4 := dist_triangle T b c e
        have c1 := dist_comm T c c'
        have c2 := dist_comm T c e
        apply le_min_add_min
        · exact min_le_of_left_le (min_le_of_left_le (by linarith))
        · exact min_le_of_left_le (min_le_of_right_le (by linarith))
        · exact min_le_of_right_le (min_le_of_left_le (by linarith))
        · exact min_le_of_right_le (min_le_of_right_le (by linarith))

/-! ### The point at depth `x` along a walk -/

/-- The point at depth `x` (from the start) along the walk `p` (clamped to the ends). -/
noncomputable def wp : {a y : Fin m} → T.G.Walk a y → ℝ → RPoint T.G
  | a, _, Walk.nil, _ => RPoint.vtx a
  | a, _, Walk.cons (v := b) h p, x =>
    if hx : x < T.w s(a, b) then
      (if hx0 : x ≤ 0 then RPoint.vtx a
       else edgePt T h (x / T.w s(a, b))
        ⟨div_pos (not_le.mp hx0) (lt_trans (not_le.mp hx0) hx),
          (div_lt_one (lt_trans (not_le.mp hx0) hx)).mpr hx⟩)
    else wp p (x - T.w s(a, b))

lemma wp_nil (a : Fin m) (x : ℝ) : wp T (Walk.nil : T.G.Walk a a) x = RPoint.vtx a := by
  rw [wp]

lemma wp_cons_rec {a b c : Fin m} (h : T.G.Adj a b) (p : T.G.Walk b c) (x : ℝ)
    (hx : ¬ x < T.w s(a, b)) : wp T (Walk.cons h p) x = wp T p (x - T.w s(a, b)) := by
  rw [wp, dif_neg hx]

lemma wp_cons_edge {a b c : Fin m} (h : T.G.Adj a b) (p : T.G.Walk b c) (x : ℝ)
    (hx0 : 0 < x) (hx : x < T.w s(a, b)) :
    ∃ hβ, wp T (Walk.cons h p) x = edgePt T h (x / T.w s(a, b)) hβ := by
  rw [wp, dif_pos hx, dif_neg (not_le.mpr hx0)]
  exact ⟨_, rfl⟩

lemma wp_end {a y : Fin m} (p : T.G.Walk a y) (x : ℝ) (hx : L T p ≤ x) :
    wp T p x = RPoint.vtx y := by
  induction p generalizing x with
  | nil => rw [wp]
  | cons h p ih =>
    rw [L_cons] at hx
    have := L_nonneg T p
    rw [wp_cons_rec T h p x (by linarith)]
    exact ih _ (by linarith)

/-- **Lemma A.** Distance from a point on a path to a node. -/
lemma wp_A {a y : Fin m} (p : T.G.Walk a y) (hp : p.IsPath) (z : Fin m) (x : ℝ) :
    rdist T (wp T p x) (RPoint.vtx z) ≤ max (T.dist a z - x) (x - L T p + T.dist y z) := by
  induction p generalizing x with
  | nil =>
    simp only [wp, rdist, L_nil]
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (by linarith)
  | @cons a a1 y h p' ih =>
    have hp' := ((Walk.cons_isPath_iff h p').mp hp).1
    have hLp' : L T p' = T.dist a1 y := (dist_eq_L T p' hp').symm
    have hR := reach_cons T h p' hp
    rw [L_cons, hLp']
    have side : (T.dist y z = T.dist a z + T.w s(a, a1) + T.dist a1 y ∧
        T.dist a1 z = T.dist a z + T.w s(a, a1)) ∨
        T.dist a z = T.w s(a, a1) + T.dist a1 z := by
      rcases MTSPTree.reach_or_reach T.isTree.connected (a := a) (b := a1) z with hz | hz
      · left
        have e1 := bridge T h hz hR
        have e2 := bridge T h hz (Reachable.refl a1)
        rw [dist_self] at e2
        rw [dist_comm T y z, e1, dist_comm T a1 z, e2, dist_comm T z a]
        constructor <;> ring
      · right
        have e := bridge T h (Reachable.refl a) hz.symm
        rw [dist_self] at e
        rw [e]; ring
    rw [wp]
    split_ifs with hx hx0
    · simp only [rdist]; exact le_max_of_le_left (by linarith)
    · have hx0' : 0 < x := not_le.mp hx0
      have hwpos : 0 < T.w s(a, a1) := lt_trans hx0' hx
      rw [rdist_edgePt_vtx]
      have e1 : x / T.w s(a, a1) * T.w s(a, a1) = x := div_mul_cancel₀ x hwpos.ne'
      have e2 : (1 - x / T.w s(a, a1)) * T.w s(a, a1) = T.w s(a, a1) - x := by
        rw [sub_mul, one_mul, e1]
      rw [e1, e2]
      rcases side with ⟨s1, s2⟩ | s1
      · exact (min_le_left _ _).trans (le_max_of_le_right (by linarith))
      · exact (min_le_right _ _).trans (le_max_of_le_left (by linarith))
    · have := ih hp' (x - T.w s(a, a1))
      rw [hLp'] at this
      refine this.trans (max_le ?_ ?_)
      · rcases side with ⟨s1, s2⟩ | s1
        · exact le_max_of_le_right (by linarith)
        · exact le_max_of_le_left (by linarith)
      · exact le_max_of_le_right (by linarith)

lemma wp_root {a y : Fin m} (p : T.G.Walk a y) (hp : p.IsPath) (x : ℝ) (hx : 0 ≤ x) :
    rdist T (wp T p x) (RPoint.vtx a) ≤ x := by
  have := wp_A T p hp a x
  rw [dist_self, dist_comm T y a, dist_eq_L T p hp] at this
  refine this.trans (max_le (by linarith) (by linarith))

lemma wp_B0 {a y z : Fin m} (p : T.G.Walk a y) (hp : p.IsPath) (q : T.G.Walk a z)
    (hq : q.IsPath) (x x' : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    rdist T (wp T p x) (wp T q x') ≤ x + x' :=
  (rdist_tri T _ _ a).trans (add_le_add (wp_root T p hp x hx)
    (by rw [rdist_comm]; exact wp_root T q hq x' hx'))

lemma wp_mix {a a1 z : Fin m} (h : T.G.Adj a a1) (q : T.G.Walk a1 z) (hq : q.IsPath)
    (x x' : ℝ) (hβ : 0 < x / T.w s(a, a1) ∧ x / T.w s(a, a1) < 1) (hx0 : 0 < x)
    (hx : x < T.w s(a, a1)) (hx' : T.w s(a, a1) ≤ x') :
    rdist T (edgePt T h (x / T.w s(a, a1)) hβ) (wp T q (x' - T.w s(a, a1))) ≤ x' - x := by
  have hwpos : 0 < T.w s(a, a1) := lt_trans hx0 hx
  refine (rdist_tri T _ _ a1).trans ?_
  rw [rdist_edgePt_vtx, rdist_comm T (RPoint.vtx a1)]
  have h2 := wp_root T q hq (x' - T.w s(a, a1)) (by linarith)
  have e1 : x / T.w s(a, a1) * T.w s(a, a1) = x := div_mul_cancel₀ x hwpos.ne'
  have e2 : (1 - x / T.w s(a, a1)) * T.w s(a, a1) = T.w s(a, a1) - x := by
    rw [sub_mul, one_mul, e1]
  rw [e2, dist_self]
  have := min_le_right (x / T.w s(a, a1) * T.w s(a, a1) + T.dist a a1) (T.w s(a, a1) - x + 0)
  linarith

/-- **Lemma B.** Distance between points on two paths from a common root. -/
lemma wp_B {a y : Fin m} (p : T.G.Walk a y) (hp : p.IsPath) {z : Fin m} (q : T.G.Walk a z)
    (hq : q.IsPath) (x x' : ℝ) (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    rdist T (wp T p x) (wp T q x') ≤ max |x - x'| (x + x' - L T p - L T q + T.dist y z) := by
  induction p generalizing z x x' with
  | nil =>
    refine le_max_of_le_right ((wp_B0 T _ hp q hq x x' hx hx').trans (le_of_eq ?_))
    rw [L_nil, dist_eq_L T q hq]; ring
  | @cons a a1 y h p' ih =>
    have hp' := ((Walk.cons_isPath_iff h p').mp hp).1
    -- the trivial cases `x = 0` or `x' = 0`
    by_cases h0 : x = 0 ∨ x' = 0
    · refine le_max_of_le_left ((wp_B0 T _ hp q hq x x' hx hx').trans ?_)
      rcases h0 with rfl | rfl
      · rw [zero_sub, abs_neg, abs_of_nonneg hx']; linarith
      · rw [sub_zero, abs_of_nonneg hx]; linarith
    push Not at h0
    have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0.1)
    have hxp' : 0 < x' := lt_of_le_of_ne hx' (Ne.symm h0.2)
    cases q with
    | nil =>
      refine le_max_of_le_right ((wp_B0 T _ hp _ hq x x' hx hx').trans (le_of_eq ?_))
      rw [L_nil, dist_comm, dist_eq_L T _ hp]; ring
    | @cons _ b1 _ h2 q' =>
      have hq' := ((Walk.cons_isPath_iff h2 q').mp hq).1
      by_cases hab : a1 = b1
      · subst hab
        have hw := T.w_nonneg s(a, a1) h
        by_cases hxw : x < T.w s(a, a1)
        · obtain ⟨hβ, e1⟩ := wp_cons_edge T h p' x hxp hxw
          rw [e1]
          by_cases hxw' : x' < T.w s(a, a1)
          · obtain ⟨hβ', e2⟩ := wp_cons_edge T h2 q' x' hxp' hxw'
            rw [e2, rdist_edgePt_same, ← sub_div, abs_div,
              abs_of_pos (lt_trans hxp hxw), div_mul_cancel₀ _ (lt_trans hxp hxw).ne']
            exact le_max_left _ _
          · rw [wp_cons_rec T h2 q' x' hxw']
            refine le_max_of_le_left ((wp_mix T h q' hq' x x' hβ hxp hxw (not_lt.mp hxw')).trans ?_)
            rw [abs_sub_comm]; exact le_abs_self _
        · rw [wp_cons_rec T h p' x hxw]
          by_cases hxw' : x' < T.w s(a, a1)
          · obtain ⟨hβ', e2⟩ := wp_cons_edge T h2 q' x' hxp' hxw'
            rw [e2, rdist_comm]
            refine le_max_of_le_left ((wp_mix T h p' hp' x' x hβ' hxp' hxw' (not_lt.mp hxw)).trans ?_)
            exact le_abs_self _
          · rw [wp_cons_rec T h2 q' x' hxw']
            have := ih hp' q' hq' (x - T.w s(a, a1)) (x' - T.w s(a, a1)) (by linarith)
              (by linarith)
            rw [L_cons, L_cons]
            refine this.trans (le_of_eq ?_)
            congr 1
            · congr 1; ring
            · ring
      · -- the paths diverge at `a`
        have hR := reach_cons T h p' hp
        have hz : (T.G.deleteEdges {s(a, a1)}).Reachable z a := by
          refine Reachable.symm ⟨(Walk.cons h2 q').toDeleteEdge _ ?_⟩
          rw [Walk.edges_cons, List.mem_cons, not_or]
          refine ⟨?_, fun he => ((Walk.cons_isPath_iff h2 q').mp hq).2
            (q'.fst_mem_support_of_mem_edges he)⟩
          intro he
          rcases Sym2.eq_iff.mp he with ⟨_, h'⟩ | ⟨_, h'⟩
          · exact hab h'
          · exact h.ne h'.symm
        have e := bridge T h hz hR
        refine le_max_of_le_right ((wp_B0 T _ hp _ hq x x' hx hx').trans (le_of_eq ?_))
        rw [dist_comm T y z, e, dist_comm T z a, dist_eq_L T _ hq, dist_eq_L T _ hp', L_cons]
        ring

end Q53



/-! Lemma 5.3 of Azarmehr–Behnezhad: the map `q : V → R(C)`. -/

namespace Q53
open MetricTSPSublinear SimpleGraph

variable {n : ℕ} {S : Finset (Fin n)}

section
variable (d : Fin n → Fin n → ℝ) (C : SteinerTree S) (s₀ : Fin n) (hs₀ : s₀ ∈ S)

/-- The root `r = ι s₀`. -/
noncomputable def root : Fin C.m := C.ι s₀

/-- The depth `D(r, ι t)` of a terminal. -/
noncomputable def Ldep (t : {s // s ∈ S}) : ℝ := C.T.dist (root C s₀) (C.ι t)

/-- A maximiser `t*` of `t ↦ D(r, ι t) − f t`. -/
noncomputable def tstar (f : {s // s ∈ S} → ℝ) : {s // s ∈ S} :=
  haveI : Nonempty {s // s ∈ S} := ⟨⟨s₀, hs₀⟩⟩
  Classical.choose (Finite.exists_max (fun t => Ldep C s₀ t - f t))

lemma tstar_spec (f : {s // s ∈ S} → ℝ) (t : {s // s ∈ S}) :
    Ldep C s₀ t - f t ≤ Ldep C s₀ (tstar C s₀ hs₀ f) - f (tstar C s₀ hs₀ f) :=
  haveI : Nonempty {s // s ∈ S} := ⟨⟨s₀, hs₀⟩⟩
  Classical.choose_spec (Finite.exists_max (fun t => Ldep C s₀ t - f t)) t

/-- `ρ(f) = max_t (D(r, ι t) − f t)`. -/
noncomputable def rho (f : {s // s ∈ S} → ℝ) : ℝ :=
  Ldep C s₀ (tstar C s₀ hs₀ f) - f (tstar C s₀ hs₀ f)

/-- The map `Φ`. -/
noncomputable def Phi (f : {s // s ∈ S} → ℝ) : RPoint C.T.G :=
  if h : ∃ s ∈ S, f = (fun t : {s // s ∈ S} => d s t) then RPoint.vtx (C.ι (Classical.choose h))
  else wp C.T (C.T.path (root C s₀) (C.ι (tstar C s₀ hs₀ f))) (max (rho C s₀ hs₀ f) 0)

/-- The target terminal `τ v` of `q_v`. -/
noncomputable def tau (v : Fin n) : {s // s ∈ S} :=
  if h : v ∈ S then ⟨v, h⟩ else tstar C s₀ hs₀ (fun t => d v t)

/-- The depth `ρ' v` of `q_v` along the root path to `ι (τ v)`. -/
noncomputable def rhoP (v : Fin n) : ℝ :=
  if h : v ∈ S then Ldep C s₀ ⟨v, h⟩ else max (rho C s₀ hs₀ (fun t => d v t)) 0

/-- The depth of the branching node of the root paths to `ι (τ u)` and `ι (τ v)`
(Gromov product). -/
noncomputable def mu (u v : Fin n) : ℝ :=
  (Ldep C s₀ (tau d C s₀ hs₀ u) + Ldep C s₀ (tau d C s₀ hs₀ v) -
    C.T.dist (C.ι (tau d C s₀ hs₀ u)) (C.ι (tau d C s₀ hs₀ v))) / 2

variable {d C s₀ hs₀}

lemma Ldep_nonneg (t : {s // s ∈ S}) : 0 ≤ Ldep C s₀ t := dist_nonneg _ _ _

lemma dist_le_Ldep_add (a b : {s // s ∈ S}) :
    C.T.dist (C.ι a) (C.ι b) ≤ Ldep C s₀ a + Ldep C s₀ b := by
  unfold Ldep
  linarith [dist_triangle C.T (C.ι a) (root C s₀) (C.ι b), dist_comm C.T (C.ι a) (root C s₀)]

lemma Ldep_sub_le (a b : {s // s ∈ S}) :
    Ldep C s₀ b - Ldep C s₀ a ≤ C.T.dist (C.ι a) (C.ι b) := by
  have := dist_triangle C.T (root C s₀) (C.ι a) (C.ι b)
  unfold Ldep; linarith

variable (hd : DoublingMST.IsMetric d)
include hd

lemma d_self (x : Fin n) : d x x = 0 := (hd.1 x x).2 rfl

lemma d_nonneg (x y : Fin n) : 0 ≤ d x y := by
  have h1 := hd.2.2 x y x
  rw [d_self hd, hd.2.1 y x] at h1
  linarith

lemma Phi_eq (v : Fin n) :
    Phi d C s₀ hs₀ (fun t => d v t) =
      wp C.T (C.T.path (root C s₀) (C.ι (tau d C s₀ hs₀ v))) (rhoP d C s₀ hs₀ v) := by
  by_cases hv : v ∈ S
  · have hex : ∃ s ∈ S, (fun t : {s // s ∈ S} => d v t) = (fun t : {s // s ∈ S} => d s t) := ⟨v, hv, rfl⟩
    unfold Phi rhoP tau
    have hw : wp C.T (C.T.path (root C s₀) (C.ι ((⟨v, hv⟩ : {s // s ∈ S}) : Fin n)))
        (Ldep C s₀ ⟨v, hv⟩) = RPoint.vtx (C.ι v) := wp_end C.T _ _ (le_of_eq rfl)
    rw [dif_pos hex, dif_pos hv, dif_pos hv, hw]
    obtain ⟨hs, he⟩ := Classical.choose_spec hex
    have := congrFun he ⟨_, hs⟩
    simp only [d_self hd] at this
    rw [← ((hd.1 _ _).1 this)]
  · have hex : ¬ ∃ s ∈ S, (fun t : {s // s ∈ S} => d v t) = (fun t : {s // s ∈ S} => d s t) := by
      rintro ⟨s, hs, he⟩
      have := congrFun he ⟨s, hs⟩
      simp only [d_self hd] at this
      exact hv (((hd.1 _ _).1 this) ▸ hs)
    unfold Phi rhoP tau
    rw [dif_neg hex, dif_neg hv, dif_neg hv]

lemma rhoP_nonneg (v : Fin n) : 0 ≤ rhoP d C s₀ hs₀ v := by
  unfold rhoP
  split_ifs
  · exact Ldep_nonneg _
  · exact le_max_right _ _

lemma rhoP_le (v : Fin n) : rhoP d C s₀ hs₀ v ≤ Ldep C s₀ (tau d C s₀ hs₀ v) := by
  unfold rhoP tau
  split_ifs with hv
  · exact le_rfl
  · refine max_le ?_ (Ldep_nonneg _)
    unfold rho
    linarith [d_nonneg hd v (tstar C s₀ hs₀ (fun t => d v t))]

variable (hC : Dominated d C)
include hC

lemma dom (a b : {s // s ∈ S}) : C.T.dist (C.ι a) (C.ι b) ≤ d a b :=
  hC a a.2 b b.2

/-- The three facts about `q_v`. -/
lemma props (v : Fin n) :
    (∀ t : {s // s ∈ S}, Ldep C s₀ t - rhoP d C s₀ hs₀ v ≤ d v t) ∧
    (∀ t : {s // s ∈ S}, rhoP d C s₀ hs₀ v - Ldep C s₀ (tau d C s₀ hs₀ v) +
      C.T.dist (C.ι (tau d C s₀ hs₀ v)) (C.ι t) ≤ d v t) ∧
    (rhoP d C s₀ hs₀ v = 0 ∨
      rhoP d C s₀ hs₀ v + d v (tau d C s₀ hs₀ v) ≤ Ldep C s₀ (tau d C s₀ hs₀ v)) := by
  unfold rhoP tau
  by_cases hv : v ∈ S
  · simp only [dif_pos hv]
    refine ⟨fun t => ?_, fun t => ?_, Or.inr ?_⟩
    · have := Ldep_sub_le (C := C) (s₀ := s₀) ⟨v, hv⟩ t
      have := dom hd hC ⟨v, hv⟩ t
      simp only at this ⊢; linarith
    · have := dom hd hC ⟨v, hv⟩ t
      simp only at this ⊢; linarith
    · simp only [d_self hd]; linarith
  · simp only [dif_neg hv]
    set f : {s // s ∈ S} → ℝ := fun t => d v t with hf
    set ts := tstar C s₀ hs₀ f with hts
    have hspec := tstar_spec C s₀ hs₀ f
    have hrho : rho C s₀ hs₀ f = Ldep C s₀ ts - d v ts := rfl
    refine ⟨fun t => ?_, fun t => ?_, ?_⟩
    · have := hspec t
      have := le_max_left (rho C s₀ hs₀ f) 0
      rw [← hts] at *
      simp only [hf] at *
      linarith
    · rcases le_total 0 (rho C s₀ hs₀ f) with hr | hr
      · rw [max_eq_left hr, hrho]
        have h1 := dom hd hC ts t
        have h2 := hd.2.2 ts v t
        have h3 := hd.2.1 ts v
        linarith
      · rw [max_eq_right hr]
        have h1 := dist_le_Ldep_add (C := C) (s₀ := s₀) ts t
        have := hspec t
        rw [← hts] at this
        simp only [hf] at this
        linarith
    · rcases le_total 0 (rho C s₀ hs₀ f) with hr | hr
      · right; rw [max_eq_left hr, hrho]; linarith
      · left; exact max_eq_right hr

/-- The key inequality. -/
lemma key (u v : Fin n) :
    max |rhoP d C s₀ hs₀ u - rhoP d C s₀ hs₀ v|
      (rhoP d C s₀ hs₀ u + rhoP d C s₀ hs₀ v - Ldep C s₀ (tau d C s₀ hs₀ u) -
        Ldep C s₀ (tau d C s₀ hs₀ v) +
        C.T.dist (C.ι (tau d C s₀ hs₀ u)) (C.ι (tau d C s₀ hs₀ v))) ≤ d u v := by
  obtain ⟨u1, u2, u3⟩ := props (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC u
  obtain ⟨v1, v2, v3⟩ := props (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC v
  set x := rhoP d C s₀ hs₀ u
  set y := rhoP d C s₀ hs₀ v
  set tu := tau d C s₀ hs₀ u
  set tv := tau d C s₀ hs₀ v
  have hx := rhoP_nonneg (C := C) (s₀ := s₀) (hs₀ := hs₀) hd u
  have hy := rhoP_nonneg (C := C) (s₀ := s₀) (hs₀ := hs₀) hd v
  have huv := d_nonneg hd u v
  have hsym := hd.2.1 u v
  have tr1 := hd.2.2 v u tu
  have tr2 := hd.2.2 u v tv
  have hD := dist_le_Ldep_add (C := C) (s₀ := s₀) tu tv
  have hDc := dist_comm C.T (C.ι tu) (C.ι tv)
  have v1u := v1 tu
  have u1v := u1 tv
  have v2u := v2 tu
  have u2v := u2 tv
  have A : x - y ≤ d u v := by
    rcases u3 with h | h
    · linarith
    · linarith
  have B : y - x ≤ d u v := by
    rcases v3 with h | h
    · linarith
    · linarith
  refine max_le (abs_sub_le_iff.mpr ⟨A, B⟩) ?_
  rcases u3 with h | h
  · linarith
  · linarith

/-- The branching-node form of the key inequality:
`ρ' u + ρ' v − 2 min(ρ' u, ρ' v, μ u v) ≤ d u v`. -/
lemma branch_le (u v : Fin n) :
    rhoP d C s₀ hs₀ u + rhoP d C s₀ hs₀ v -
      2 * min (min (rhoP d C s₀ hs₀ u) (rhoP d C s₀ hs₀ v)) (mu d C s₀ hs₀ u v) ≤ d u v := by
  refine le_trans ?_ (key (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC u v)
  unfold mu
  set x := rhoP d C s₀ hs₀ u
  set y := rhoP d C s₀ hs₀ v
  rcases le_total (min x y) ((Ldep C s₀ (tau d C s₀ hs₀ u) + Ldep C s₀ (tau d C s₀ hs₀ v) -
    C.T.dist (C.ι (tau d C s₀ hs₀ u)) (C.ι (tau d C s₀ hs₀ v))) / 2) with h | h
  · rw [min_eq_left h]
    refine le_max_of_le_left ?_
    rcases le_total x y with h' | h'
    · rw [min_eq_left h', abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · rw [min_eq_right h', abs_of_nonneg (by linarith)]; linarith
  · rw [min_eq_right h]
    exact le_max_of_le_right (le_of_eq (by ring))

/-- Non-expansiveness of `q`. -/
lemma Phi_le (u v : Fin n) :
    rdist C.T (Phi d C s₀ hs₀ (fun t => d u t)) (Phi d C s₀ hs₀ (fun t => d v t)) ≤ d u v := by
  rw [Phi_eq (C := C) (s₀ := s₀) (hs₀ := hs₀) hd, Phi_eq (C := C) (s₀ := s₀) (hs₀ := hs₀) hd]
  exact (wp_B C.T _ (path_isPath _ _ _) _ (path_isPath _ _ _) _ _
    (rhoP_nonneg (C := C) (s₀ := s₀) (hs₀ := hs₀) hd u) (rhoP_nonneg (C := C) (s₀ := s₀) (hs₀ := hs₀) hd v)).trans (key (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC u v)

lemma Phi_vtx (s : Fin n) (hs : s ∈ S) :
    Phi d C s₀ hs₀ (fun t => d s t) = RPoint.vtx (C.ι s) := by
  rw [Phi_eq (C := C) (s₀ := s₀) (hs₀ := hs₀) hd]
  unfold rhoP tau
  rw [dif_pos hs, dif_pos hs]
  exact wp_end C.T _ _ (le_of_eq rfl)

end

end Q53

open MetricTSPSublinear in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (hd : DoublingMST.IsMetric d) (S : Finset (Fin n)) (C : SteinerTree S)
    (hC : Dominated d C) :
    ∃ Φ : ({s // s ∈ S} → ℝ) → RPoint C.T.G,
      (∀ s ∈ S, Φ (fun t => d s t) = RPoint.vtx (C.ι s)) ∧
      ∀ u v, rdist C.T (Φ (fun t => d u t)) (Φ (fun t => d v t)) ≤ d u v := by
  rcases S.eq_empty_or_nonempty with hS | ⟨s₀, hs₀⟩
  · obtain ⟨a⟩ := C.T.isTree.connected.nonempty
    refine ⟨fun _ => RPoint.vtx a, fun s hs => by simp [hS] at hs, fun u v => ?_⟩
    simp only [rdist, Q53.dist_self]
    exact Q53.d_nonneg hd u v
  · exact ⟨Q53.Phi d C s₀ hs₀, fun s hs => Q53.Phi_vtx (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC s hs,
      fun u v => Q53.Phi_le (C := C) (s₀ := s₀) (hs₀ := hs₀) hd hC u v⟩
