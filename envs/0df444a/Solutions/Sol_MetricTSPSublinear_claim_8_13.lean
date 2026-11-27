-- Prove2me | solution 1 for MetricTSPSublinear.claim_8_13
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:43:05.569809+00:00
-- url     : https://prove2.me/submissions/2ef64cf9-0933-4784-ac40-358c114f76ac

import Definitions.Def_DoublingMST_edgeCost
import Definitions.Def_MetricTSPSublinear_treeDist
import Mathlib
import Definitions.Def_MetricTSPSublinear_IsAdmissibleFragShortening

section ASM0
-- from Solutions.C813.Tree

/-!
# Tree-path lemmas for `MetricTSPSublinear.pathEdges` (used for Claim 8.13)
-/

open scoped Classical

namespace MTSP813
open SimpleGraph MetricTSPSublinear

variable {n : ℕ}

/-- The graph of an edge set. -/
abbrev graphOf (E : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))

lemma pathEdges_subset (E : Finset (Sym2 (Fin n))) (u v : Fin n) : pathEdges E u v ⊆ E :=
  Finset.filter_subset _ _

lemma mem_pathEdges {E : Finset (Sym2 (Fin n))} {u v : Fin n} {e : Sym2 (Fin n)} :
    e ∈ pathEdges E u v ↔
      e ∈ E ∧ ¬ (SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {e})).Reachable u v := by
  unfold pathEdges; simp

/-- Triangle inclusion for separating edges (no tree hypothesis needed). -/
lemma pathEdges_triangle (E : Finset (Sym2 (Fin n))) (u v w : Fin n) :
    pathEdges E u w ⊆ pathEdges E u v ∪ pathEdges E v w := by
  intro e he
  rw [mem_pathEdges] at he
  rw [Finset.mem_union, mem_pathEdges, mem_pathEdges]
  by_contra h
  push Not at h
  exact he.2 ((h.1 he.1).trans (h.2 he.1))

/-- A walk avoiding `e` witnesses reachability after deleting `e`. -/
lemma reach_of_not_mem {E : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)} :
    ∀ {u v : Fin n} (q : (graphOf E).Walk u v), e ∉ q.edges →
      (SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {e})).Reachable u v := by
  intro u v q
  induction q with
  | nil => intro _; exact Reachable.refl _
  | @cons a b c h q ih =>
    intro he
    rw [Walk.edges_cons, List.mem_cons, not_or] at he
    have hadj : (SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {e})).Adj a b := by
      rw [fromEdgeSet_adj] at h ⊢
      exact ⟨⟨h.1, fun h' => he.1 (h'.symm ▸ rfl)⟩, h.2⟩
    exact hadj.reachable.trans (ih he.2)

/-- Separating edges lie on every walk. -/
lemma pathEdges_subset_walk {E : Finset (Sym2 (Fin n))} {u v : Fin n} (q : (graphOf E).Walk u v) :
    ∀ e ∈ pathEdges E u v, e ∈ q.edges := by
  intro e he
  by_contra h
  exact (mem_pathEdges.mp he).2 (reach_of_not_mem q h)

/-- In an acyclic graph every edge of a path separates its endpoints. -/
lemma mem_pathEdges_of_path {E : Finset (Sym2 (Fin n))} (hac : (graphOf E).IsAcyclic) {u v : Fin n}
    (p : (graphOf E).Walk u v) (hp : p.IsPath) : ∀ e ∈ p.edges, e ∈ pathEdges E u v := by
  intro e he
  have heE : e ∈ E := by
    have := p.edges_subset_edgeSet he
    rw [edgeSet_fromEdgeSet] at this
    exact this.1
  rw [mem_pathEdges]
  refine ⟨heE, ?_⟩
  rintro ⟨q⟩
  have hle : SimpleGraph.fromEdgeSet ((E : Set (Sym2 (Fin n))) \ {e}) ≤ graphOf E :=
    fromEdgeSet_mono Set.sdiff_subset
  let q' := q.bypass
  have hq' : q'.IsPath := q.bypass_isPath
  have heq : (⟨q'.mapLe hle, hq'.mapLe hle⟩ : (graphOf E).Path u v) = ⟨p, hp⟩ :=
    (hac.subsingleton_path u v).elim _ _
  have hmem : e ∈ (q'.mapLe hle).edges := by
    have := congrArg Subtype.val heq
    simp only at this
    rw [this]; exact he
  rw [Walk.edges_mapLe_eq_edges] at hmem
  have := q'.edges_subset_edgeSet hmem
  rw [edgeSet_fromEdgeSet] at this
  exact this.1.2 rfl

/-- First exit of a walk from a vertex set. -/
lemma walk_exit (F : Finset (Fin n)) {G : SimpleGraph (Fin n)} :
    ∀ {v x : Fin n} (p : G.Walk v x), v ∈ F → x ∉ F →
      ∃ b c, ∃ h : G.Adj b c, ∃ q : G.Walk v b, ∃ r : G.Walk c x,
        b ∈ F ∧ c ∉ F ∧ p = q.append (Walk.cons h r) := by
  intro v x p
  induction p with
  | nil => intro hv hx; exact absurd hv hx
  | @cons a y z h p ih =>
    intro ha hz
    by_cases hy : y ∈ F
    · obtain ⟨b, c, hbc, q, r, hb, hc, hp⟩ := ih hy hz
      exact ⟨b, c, hbc, Walk.cons h q, r, hb, hc, by rw [hp, Walk.cons_append]⟩
    · exact ⟨a, y, h, Walk.nil, p, ha, hy, by rw [Walk.nil_append]⟩

/-- **Exit edge.** In a tree, for `v ∈ F` and `x ∉ F` there is an edge `{b, c}` of the `v`–`x` path with `b ∈ F`,
`c ∉ F`, and the `v`–`b` path is contained in the `v`–`x` path minus `{b, c}`. -/
lemma exists_exit_edge {E : Finset (Sym2 (Fin n))} (hT : (graphOf E).IsTree) (F : Finset (Fin n))
    {v x : Fin n} (hv : v ∈ F) (hx : x ∉ F) :
    ∃ b c, b ∈ F ∧ c ∉ F ∧ s(b, c) ∈ E ∧ s(b, c) ∈ pathEdges E v x ∧
      pathEdges E v b ⊆ (pathEdges E v x).erase s(b, c) := by
  obtain ⟨p0⟩ := hT.connected.preconnected v x
  let p := p0.bypass
  have hp : p.IsPath := p0.bypass_isPath
  obtain ⟨b, c, hbc, q, r, hb, hc, hpq⟩ := walk_exit F p hv hx
  have hedges : p.edges = q.edges ++ s(b, c) :: r.edges := by
    rw [hpq, Walk.edges_append, Walk.edges_cons]
  have hnd := hp.isTrail.edges_nodup
  rw [hedges] at hnd
  have hbcq : s(b, c) ∉ q.edges := by
    intro hm
    rw [List.nodup_append] at hnd
    exact hnd.2.2 _ hm _ List.mem_cons_self rfl
  have hsub : ∀ e ∈ q.edges, e ∈ pathEdges E v x := fun e he =>
    mem_pathEdges_of_path hT.isAcyclic p hp e (by rw [hedges]; exact List.mem_append_left _ he)
  have hbcmem : s(b, c) ∈ pathEdges E v x :=
    mem_pathEdges_of_path hT.isAcyclic p hp _ (by rw [hedges]; simp)
  refine ⟨b, c, hb, hc, pathEdges_subset E v x hbcmem, hbcmem, ?_⟩
  intro e he
  have heq := pathEdges_subset_walk q e he
  rw [Finset.mem_erase]
  exact ⟨fun h => hbcq (h ▸ heq), hsub e heq⟩

/-- Sum of a weight over the path edges. -/
lemma treeDist_triangle (E : Finset (Sym2 (Fin n))) (f : Sym2 (Fin n) → ℝ) (hf : ∀ e ∈ E, 0 ≤ f e)
    (u v w : Fin n) : treeDist E f u w ≤ treeDist E f u v + treeDist E f v w := by
  unfold treeDist
  have h1 : ∑ e ∈ pathEdges E u w, f e ≤ ∑ e ∈ pathEdges E u v ∪ pathEdges E v w, f e :=
    Finset.sum_le_sum_of_subset_of_nonneg (pathEdges_triangle E u v w) (fun e he _ => by
      rcases Finset.mem_union.mp he with h | h
      · exact hf e (pathEdges_subset E u v h)
      · exact hf e (pathEdges_subset E v w h))
  have h2 := Finset.sum_union_inter (s₁ := pathEdges E u v) (s₂ := pathEdges E v w) (f := f)
  have h3 : 0 ≤ ∑ e ∈ pathEdges E u v ∩ pathEdges E v w, f e :=
    Finset.sum_nonneg (fun e he => hf e (pathEdges_subset E u v (Finset.mem_inter.mp he).1))
  linarith

lemma treeDist_mono (E : Finset (Sym2 (Fin n))) {f g : Sym2 (Fin n) → ℝ} (h : ∀ e ∈ E, f e ≤ g e)
    (u v : Fin n) : treeDist E f u v ≤ treeDist E g u v :=
  Finset.sum_le_sum (fun e he => h e (pathEdges_subset E u v he))

/-- Exit-edge distance bound: `d_f(v, b) + f(b, c) ≤ d_f(v, x)`. -/
lemma exit_bound {E : Finset (Sym2 (Fin n))} (hT : (graphOf E).IsTree) (F : Finset (Fin n))
    {v x : Fin n} (hv : v ∈ F) (hx : x ∉ F) (f : Sym2 (Fin n) → ℝ) (hf : ∀ e ∈ E, 0 ≤ f e) :
    ∃ b c, b ∈ F ∧ c ∉ F ∧ s(b, c) ∈ E ∧ treeDist E f v b + f s(b, c) ≤ treeDist E f v x := by
  obtain ⟨b, c, hb, hc, hE, hmem, hsub⟩ := exists_exit_edge hT F hv hx
  refine ⟨b, c, hb, hc, hE, ?_⟩
  unfold treeDist
  rw [← Finset.add_sum_erase _ _ hmem]
  have : ∑ e ∈ pathEdges E v b, f e ≤ ∑ e ∈ (pathEdges E v x).erase s(b, c), f e :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e he _ =>
      hf e (pathEdges_subset E v x (Finset.mem_of_mem_erase he)))
  linarith

end MTSP813

end ASM0

section ASM1
-- from Solutions.C813.Correct

/-!
# Path corrections: lowering nonnegative weights so that given path sums meet given bounds,
at cost at most the total excess.
-/

open scoped Classical

namespace MTSP813

/-- One correction: scale the weights on `P` down so that their sum is at most `b`. -/
lemma correct_one {α : Type*} [Fintype α] (s : α → ℝ) (hs : ∀ e, 0 ≤ s e) (P : Finset α) (b : ℝ)
    (hb : 0 ≤ b) :
    ∃ s' : α → ℝ, (∀ e, 0 ≤ s' e) ∧ (∀ e, s' e ≤ s e) ∧ ∑ e ∈ P, s' e ≤ b ∧
      ∑ e, (s e - s' e) ≤ max 0 (∑ e ∈ P, s e - b) := by
  by_cases h : ∑ e ∈ P, s e ≤ b
  · exact ⟨s, hs, fun _ => le_rfl, h, by simp⟩
  · push Not at h
    set σ := ∑ e ∈ P, s e with hσ
    have hσpos : 0 < σ := lt_of_le_of_lt hb h
    have hq0 : 0 ≤ b / σ := div_nonneg hb hσpos.le
    have hq1 : b / σ ≤ 1 := (div_le_one hσpos).mpr h.le
    refine ⟨fun e => if e ∈ P then s e * (b / σ) else s e, ?_, ?_, ?_, ?_⟩
    · intro e; dsimp only; split_ifs
      · exact mul_nonneg (hs e) hq0
      · exact hs e
    · intro e; dsimp only; split_ifs
      · exact mul_le_of_le_one_right (hs e) hq1
      · exact le_rfl
    · have : ∑ e ∈ P, (if e ∈ P then s e * (b / σ) else s e) = ∑ e ∈ P, s e * (b / σ) :=
        Finset.sum_congr rfl (fun e he => by rw [if_pos he])
      rw [this, ← Finset.sum_mul, ← hσ, mul_div_cancel₀ _ hσpos.ne']
    · have h1 : ∑ e, (s e - if e ∈ P then s e * (b / σ) else s e) =
          ∑ e ∈ P, (s e - if e ∈ P then s e * (b / σ) else s e) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ P)
        intro e _ he; rw [if_neg he]; ring
      have h2 : ∑ e ∈ P, (s e - if e ∈ P then s e * (b / σ) else s e) = σ - b := by
        rw [Finset.sum_congr rfl (fun e he => by rw [if_pos he])]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← hσ, mul_div_cancel₀ _ hσpos.ne']
      rw [h1, h2]; exact le_max_right _ _

/-- Iterated corrections over a finite family of (path, bound) constraints. -/
lemma correct_all {α κ : Type*} [Fintype α] (c : α → ℝ) (hc : ∀ e, 0 ≤ c e) (P : κ → Finset α)
    (b : κ → ℝ) (K : Finset κ) (hb : ∀ k ∈ K, 0 ≤ b k) :
    ∃ s : α → ℝ, (∀ e, 0 ≤ s e) ∧ (∀ e, s e ≤ c e) ∧ (∀ k ∈ K, ∑ e ∈ P k, s e ≤ b k) ∧
      ∑ e, (c e - s e) ≤ ∑ k ∈ K, max 0 (∑ e ∈ P k, c e - b k) := by
  induction K using Finset.induction_on with
  | empty => exact ⟨c, hc, fun _ => le_rfl, by simp, by simp⟩
  | @insert k K hk ih =>
    obtain ⟨s, hs0, hsc, hsK, hcost⟩ := ih (fun k' hk' => hb k' (Finset.mem_insert_of_mem hk'))
    obtain ⟨s', hs'0, hs's, hs'P, hcost'⟩ :=
      correct_one s hs0 (P k) (b k) (hb k (Finset.mem_insert_self k K))
    refine ⟨s', hs'0, fun e => (hs's e).trans (hsc e), ?_, ?_⟩
    · intro k' hk'
      rcases Finset.mem_insert.mp hk' with rfl | hk'
      · exact hs'P
      · exact (Finset.sum_le_sum (fun e _ => hs's e)).trans (hsK k' hk')
    · rw [Finset.sum_insert hk]
      have hsplit : ∑ e, (c e - s' e) = ∑ e, (c e - s e) + ∑ e, (s e - s' e) := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun e _ => by ring)
      have hmono : max 0 (∑ e ∈ P k, s e - b k) ≤ max 0 (∑ e ∈ P k, c e - b k) := by
        apply max_le_max le_rfl
        linarith [Finset.sum_le_sum (fun e (_ : e ∈ P k) => hsc e)]
      linarith

end MTSP813

end ASM1

section ASM2
-- from Solutions.C813.Main

/-!
# Claim 8.13 of Azarmehr–Behnezhad (arXiv:2611.04283), without the discretization term

Optimal admissible fragment shortenings (constraints (10)) retain
`w_T(E \ H) + (1 - 1/λ) A_H - 2 D_U` of weight.
-/

open scoped Classical

namespace MTSP813
open MetricTSPSublinear

variable {n : ℕ}

/-- The tree edges with both endpoints in `F`. -/
def insideEdges (E : Finset (Sym2 (Fin n))) (F : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  E.filter (fun e => ∀ z ∈ e, z ∈ F)

/-- Ordered pairs `(v, x)` with `{v, x}` a tree edge, `v ∈ F`, `x ∉ F`. -/
def crossPairs (E : Finset (Sym2 (Fin n))) (F : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => s(p.1, p.2) ∈ E ∧ p.1 ∈ F ∧ p.2 ∉ F)

/-- **Admissible shortening of a fragment** `F` with root `o` (paper (10)): weights supported on the tree edges
inside `F`, between `0` and the MST weight, with
(i) `d_t(u, v) ≤ d(u, v)` for `u, v ∈ F`, (ii) `d_t(v, o) ≤ d(v, x)` for `v ∈ F`, `x ∉ F`,
(iii) `d_t(v, o) ≤ λ r` for `v ∈ F`. -/
def Admissible (d : Fin n → Fin n → ℝ) (E : Finset (Sym2 (Fin n))) (F : Finset (Fin n)) (o : Fin n)
    (lam r : ℝ) (t : Sym2 (Fin n) → ℝ) : Prop :=
  (∀ e, e ∉ insideEdges E F → t e = 0) ∧
  (∀ e ∈ E, 0 ≤ t e ∧ t e ≤ DoublingMST.edgeCost d e) ∧
  (∀ u ∈ F, ∀ v ∈ F, treeDist E t u v ≤ d u v) ∧
  (∀ v ∈ F, ∀ x ∉ F, treeDist E t v o ≤ d v x) ∧
  (∀ v ∈ F, treeDist E t v o ≤ lam * r)

lemma edgeCost_mk (d : Fin n → Fin n → ℝ) (hsymm : ∀ u v, d u v = d v u) (a b : Fin n) :
    DoublingMST.edgeCost d s(a, b) = d a b := by
  simp only [DoublingMST.edgeCost, Sym2.lift_mk, hsymm b a, min_self]

lemma insideEdges_subset (E : Finset (Sym2 (Fin n))) (F : Finset (Fin n)) : insideEdges E F ⊆ E :=
  Finset.filter_subset _ _

/-- **Per-fragment construction** (proof of Claim 8.13): from any admissible `t` build an admissible `t'` whose
weight is at least the right-hand side. -/
lemma fragment_bound (d : Fin n → Fin n → ℝ) (hsymm : ∀ u v, d u v = d v u)
    (E : Finset (Sym2 (Fin n))) (hT : (graphOf E).IsTree)
    (U : Sym2 (Fin n) → ℝ) (hU : ∀ e ∈ E, 0 ≤ U e ∧ U e ≤ DoublingMST.edgeCost d e)
    (hUd : ∀ u v, treeDist E U u v ≤ d u v)
    (F : Finset (Fin n)) (o : Fin n) (H : Finset (Sym2 (Fin n))) (lam r : ℝ) (hlam : 1 ≤ lam)
    (hH2 : ∀ b c, s(b, c) ∈ E → b ∈ F → c ∉ F → pathEdges E b o ⊆ H)
    (hH3 : ∀ v ∈ F, ∃ a ∈ F, pathEdges E a o ⊆ H ∧ treeDist E U v a ≤ r)
    (t : Sym2 (Fin n) → ℝ) (ht : Admissible d E F o lam r t) :
    ∃ t', Admissible d E F o lam r t' ∧
      (∑ e ∈ E, (if e ∈ insideEdges E F ∧ e ∉ H then DoublingMST.edgeCost d e else 0))
        + (1 - 1 / lam) * ∑ e ∈ E ∩ H, t e
        - (∑ e ∈ E, (if e ∈ insideEdges E F then DoublingMST.edgeCost d e - U e else 0)
          + ∑ p ∈ crossPairs E F, (DoublingMST.edgeCost d s(p.1, p.2) - U s(p.1, p.2)))
        ≤ ∑ e ∈ E, t' e := by
  obtain ⟨htsupp, htw, _htdom, htout, htdep⟩ := ht
  set w := DoublingMST.edgeCost d with hw
  set I := insideEdges E F with hI
  set κ := 1 - 1 / lam with hκ
  have hlam0 : 0 < lam := by linarith
  have hκ0 : 0 ≤ κ := by
    rw [hκ, sub_nonneg, div_le_one hlam0]; exact hlam
  have hκ1 : κ ≤ 1 := by
    rw [hκ]; have : 0 ≤ 1 / lam := by positivity
    linarith
  have hIE : ∀ {e}, e ∈ I → e ∈ E := fun he => insideEdges_subset E F he
  have ht0 : ∀ e, 0 ≤ t e := by
    intro e
    by_cases he : e ∈ I
    · exact (htw e (hIE he)).1
    · rw [htsupp e he]
  -- step 1: clamp
  let c : Sym2 (Fin n) → ℝ := fun e => if e ∈ I then min (t e) (U e) else 0
  have hc0 : ∀ e, 0 ≤ c e := by
    intro e; simp only [c]; split_ifs with he
    · exact le_min (ht0 e) (hU e (hIE he)).1
    · exact le_rfl
  have hct : ∀ e, c e ≤ t e := by
    intro e; simp only [c]; split_ifs with he
    · exact min_le_left _ _
    · exact ht0 e
  have hcU : ∀ e ∈ I, c e ≤ U e := by
    intro e he; simp only [c, if_pos he]; exact min_le_right _ _
  -- step 2: path corrections
  obtain ⟨s, hs0, hsc, hsK, hcost⟩ := correct_all c hc0 (fun p => pathEdges E p.1 o)
    (fun p => U s(p.1, p.2)) (crossPairs E F) (fun p hp => (hU _ (Finset.mem_filter.mp hp).2.1).1)
  -- steps 3–4: scale inside H, restore `U` outside H
  let t' : Sym2 (Fin n) → ℝ := fun e => if e ∈ I then (if e ∈ H then κ * s e else U e) else 0
  have ht'0 : ∀ e, 0 ≤ t' e := by
    intro e; simp only [t']; split_ifs with h1 h2
    · exact mul_nonneg hκ0 (hs0 e)
    · exact (hU e (hIE h1)).1
    · exact le_rfl
  have ht'U : ∀ e ∈ E, t' e ≤ U e := by
    intro e heE; simp only [t']; split_ifs with h1 h2
    · calc κ * s e ≤ s e := mul_le_of_le_one_left (hs0 e) hκ1
        _ ≤ c e := hsc e
        _ ≤ U e := hcU e h1
    · exact le_rfl
    · exact (hU e heE).1
  have ht's : ∀ e ∈ H, t' e ≤ s e := by
    intro e heH; simp only [t']; split_ifs with h1
    · exact mul_le_of_le_one_left (hs0 e) hκ1
    · exact hs0 e
  have ht't : ∀ e ∈ H, t' e ≤ κ * t e := by
    intro e heH; simp only [t']; split_ifs with h1
    · exact mul_le_mul_of_nonneg_left ((hsc e).trans (hct e)) hκ0
    · exact mul_nonneg hκ0 (ht0 e)
  refine ⟨t', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e he; exact if_neg he
  · intro e he; exact ⟨ht'0 e, (ht'U e he).trans (hU e he).2⟩
  · intro u _ v _
    exact (treeDist_mono E ht'U u v).trans (hUd u v)
  · -- (ii)
    intro v hv x hx
    obtain ⟨b, c', hb, hc', hbcE, hineq⟩ := exit_bound hT F hv hx U (fun e he => (hU e he).1)
    have h1 := treeDist_triangle E t' (fun e _ => ht'0 e) v b o
    have h2 := treeDist_mono E ht'U v b
    have h3 : treeDist E t' b o ≤ U s(b, c') := by
      have hmem : (b, c') ∈ crossPairs E F := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbcE, hb, hc'⟩
      refine le_trans ?_ (hsK (b, c') hmem)
      exact Finset.sum_le_sum (fun e he => ht's e (hH2 b c' hbcE hb hc' he))
    linarith [hUd v x]
  · -- (iii)
    intro v hv
    obtain ⟨a, ha, haH, hva⟩ := hH3 v hv
    have h1 := treeDist_triangle E t' (fun e _ => ht'0 e) v a o
    have h2 := treeDist_mono E ht'U v a
    have h3 : treeDist E t' a o ≤ κ * treeDist E t a o := by
      unfold treeDist; rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun e he => ht't e (haH he))
    have h4 : κ * treeDist E t a o ≤ κ * (lam * r) := mul_le_mul_of_nonneg_left (htdep a ha) hκ0
    have h5 : κ * (lam * r) = lam * r - r := by
      rw [hκ]; field_simp
    linarith
  · -- weight accounting
    have hcross : ∑ e, (c e - s e) ≤
        ∑ p ∈ crossPairs E F, (w s(p.1, p.2) - U s(p.1, p.2)) := by
      refine hcost.trans (Finset.sum_le_sum (fun p hp => ?_))
      obtain ⟨-, hpE, hp1, hp2⟩ := Finset.mem_filter.mp hp
      refine max_le (sub_nonneg.mpr (hU _ hpE).2) ?_
      have h1 : ∑ e ∈ pathEdges E p.1 o, c e ≤ treeDist E t p.1 o :=
        Finset.sum_le_sum (fun e _ => hct e)
      have h2 := htout p.1 hp1 p.2 hp2
      have h3 : w s(p.1, p.2) = d p.1 p.2 := edgeCost_mk d hsymm _ _
      linarith
    have hEH : ∑ e ∈ E ∩ H, t e = ∑ e ∈ E, (if e ∈ H then t e else 0) := by
      rw [← Finset.filter_mem_eq_inter, Finset.sum_filter]
    have hcs : ∑ e ∈ E, (if e ∈ H then c e - s e else 0) ≤ ∑ e, (c e - s e) := by
      refine (Finset.sum_le_sum (fun e _ => ?_)).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ E)
          (fun e _ _ => sub_nonneg.mpr (hsc e)))
      split_ifs
      · exact le_rfl
      · exact sub_nonneg.mpr (hsc e)
    have hper : ∀ e ∈ E, (if e ∈ I ∧ e ∉ H then w e else 0) + κ * (if e ∈ H then t e else 0)
        - (if e ∈ I then w e - U e else 0) - (if e ∈ H then c e - s e else 0) ≤ t' e := by
      intro e heE
      have hsce := hsc e
      have hs0e := hs0 e
      by_cases hIe : e ∈ I
      · have hce : c e = min (t e) (U e) := by simp only [c, if_pos hIe]
        have htw' := htw e heE
        have hUe := hU e heE
        by_cases hHe : e ∈ H
        · have ht'e : t' e = κ * s e := by simp only [t', if_pos hIe, if_pos hHe]
          have p1 : κ * (t e - c e) ≤ t e - c e :=
            mul_le_of_le_one_left (by rw [hce]; exact sub_nonneg.mpr (min_le_left _ _)) hκ1
          have p2 : 0 ≤ (1 - κ) * (c e - s e) := mul_nonneg (by linarith) (by linarith)
          have p3 : t e - c e ≤ w e - U e := by
            rw [hce]; rcases min_choice (t e) (U e) with h | h <;> rw [h] <;> linarith
          simp only [hIe, hHe, not_true_eq_false, and_false, if_false, if_true]
          rw [ht'e]; nlinarith
        · have ht'e : t' e = U e := by simp only [t', if_pos hIe, if_neg hHe]
          simp only [hIe, hHe, not_false_eq_true, and_self, if_false, if_true]
          rw [ht'e]; linarith
      · have ht'e : t' e = 0 := by simp only [t', if_neg hIe]
        have hce : c e = 0 := by simp only [c, if_neg hIe]
        have hte : t e = 0 := htsupp e hIe
        simp only [hIe, false_and, if_false, ht'e, hce, hte]
        split_ifs <;> linarith
    have hsum := Finset.sum_le_sum hper
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      at hsum
    rw [hEH]
    linarith

lemma sum_indicator_le_one {ι : Type*} [Fintype ι] (F : ι → Finset (Fin n))
    (hF : Pairwise fun j k => Disjoint (F j) (F k)) (a : Fin n) :
    ∑ j, (if a ∈ F j then (1 : ℝ) else 0) ≤ 1 := by
  rw [Finset.sum_boole]
  exact_mod_cast Finset.card_le_one.mpr (fun j hj k hk => by
    by_contra hne
    exact Finset.disjoint_left.mp (hF hne) (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2)

lemma crossPairs_injOn (E : Finset (Sym2 (Fin n))) (F : Finset (Fin n)) :
    Set.InjOn (fun p : Fin n × Fin n => s(p.1, p.2)) (crossPairs E F) := by
  intro p hp q hq hpq
  obtain ⟨-, -, hp1, hp2⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, -, hq1, hq2⟩ := Finset.mem_filter.mp hq
  rcases Sym2.eq_iff.mp hpq with ⟨h1, h2⟩ | ⟨h1, _⟩
  · exact Prod.ext h1 h2
  · exact absurd (h1 ▸ hp1) hq2

/-- Each tree edge is charged at most twice: once as an inside edge or once per endpoint as a crossing edge. -/
lemma charge_le_two {ι : Type*} [Fintype ι] (F : ι → Finset (Fin n))
    (hF : Pairwise fun j k => Disjoint (F j) (F k)) (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    ∑ j, ((if e ∈ insideEdges E (F j) then (1 : ℝ) else 0) +
      (if e ∈ (crossPairs E (F j)).image (fun p => s(p.1, p.2)) then 1 else 0)) ≤ 2 := by
  induction e using Sym2.ind with
  | h a b =>
  have key : ∀ j, (if s(a, b) ∈ insideEdges E (F j) then (1 : ℝ) else 0) +
      (if s(a, b) ∈ (crossPairs E (F j)).image (fun p => s(p.1, p.2)) then 1 else 0) ≤
      (if a ∈ F j then 1 else 0) + (if b ∈ F j then 1 else 0) := by
    intro j
    by_cases h1 : s(a, b) ∈ insideEdges E (F j)
    · have hz := (Finset.mem_filter.mp h1).2
      have ha : a ∈ F j := hz a (Sym2.mem_mk_left a b)
      have hb : b ∈ F j := hz b (Sym2.mem_mk_right a b)
      have h2 : s(a, b) ∉ (crossPairs E (F j)).image (fun p => s(p.1, p.2)) := by
        intro hm
        obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hm
        obtain ⟨-, -, -, hp2⟩ := Finset.mem_filter.mp hp
        exact hp2 (hz p.2 (hpe ▸ Sym2.mem_mk_right p.1 p.2))
      rw [if_pos h1, if_neg h2, if_pos ha, if_pos hb]; norm_num
    · rw [if_neg h1]
      by_cases h2 : s(a, b) ∈ (crossPairs E (F j)).image (fun p => s(p.1, p.2))
      · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp h2
        obtain ⟨-, -, hp1, -⟩ := Finset.mem_filter.mp hp
        have hmem : p.1 ∈ s(a, b) := hpe ▸ Sym2.mem_mk_left p.1 p.2
        rw [if_pos h2]
        rcases Sym2.mem_iff.mp hmem with h | h
        · have haF : a ∈ F j := by rw [← h]; exact hp1
          rw [if_pos haF]; split_ifs <;> norm_num
        · have hbF : b ∈ F j := by rw [← h]; exact hp1
          rw [if_pos hbF]; split_ifs <;> norm_num
      · rw [if_neg h2]; split_ifs <;> norm_num
  calc _ ≤ ∑ j, ((if a ∈ F j then (1 : ℝ) else 0) + (if b ∈ F j then 1 else 0)) :=
        Finset.sum_le_sum (fun j _ => key j)
    _ = ∑ j, (if a ∈ F j then (1 : ℝ) else 0) + ∑ j, (if b ∈ F j then (1 : ℝ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ 1 + 1 := add_le_add (sum_indicator_le_one F hF a) (sum_indicator_le_one F hF b)
    _ = 2 := by norm_num

/-- **Claim 8.13** (Azarmehr–Behnezhad, arXiv:2611.04283, §8.2, pp.30–31), without the discretization term `nσ`.

For optimal admissible shortenings `t j` of the fragments `F j` (constraints (10)),
`Σ_j w(t_j) ≥ w_T(E \ H) + (1 - 1/λ) A_H - 2 D_U`, where `A_H = Σ_j Σ_{e ∈ E ∩ H} t_j(e)` and
`D_U = Σ_{e ∈ E} (w_T(e) - U(e))`. -/
theorem claim_8_13 {ι : Type*} [Fintype ι] (d : Fin n → Fin n → ℝ) (hsymm : ∀ u v, d u v = d v u)
    (E : Finset (Sym2 (Fin n))) (hT : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).IsTree)
    (U : Sym2 (Fin n) → ℝ) (hU : ∀ e ∈ E, 0 ≤ U e ∧ U e ≤ DoublingMST.edgeCost d e)
    (hUd : ∀ u v, treeDist E U u v ≤ d u v)
    (F : ι → Finset (Fin n)) (hF : Pairwise fun j k => Disjoint (F j) (F k)) (o : ι → Fin n)
    (H : Finset (Sym2 (Fin n))) (lam r : ℝ) (hlam : 1 ≤ lam)
    (hH1 : ∀ e ∈ E, e ∉ H → ∃ j, ∀ z ∈ e, z ∈ F j)
    (hH2 : ∀ j b c, s(b, c) ∈ E → b ∈ F j → c ∉ F j → pathEdges E b (o j) ⊆ H)
    (hH3 : ∀ j, ∀ v ∈ F j, ∃ a ∈ F j, pathEdges E a (o j) ⊆ H ∧ treeDist E U v a ≤ r)
    (t : ι → Sym2 (Fin n) → ℝ) (ht : ∀ j, Admissible d E (F j) (o j) lam r (t j))
    (hopt : ∀ j t', Admissible d E (F j) (o j) lam r t' → ∑ e ∈ E, t' e ≤ ∑ e ∈ E, t j e) :
    ∑ e ∈ E \ H, DoublingMST.edgeCost d e + (1 - 1 / lam) * ∑ j, ∑ e ∈ E ∩ H, t j e
      - 2 * ∑ e ∈ E, (DoublingMST.edgeCost d e - U e)
      ≤ ∑ j, ∑ e ∈ E, t j e := by
  set w := DoublingMST.edgeCost d with hw
  choose t' ht'adm ht'bd using fun j =>
    fragment_bound d hsymm E hT U hU hUd (F j) (o j) H lam r hlam (hH2 j) (hH3 j) (t j) (ht j)
  have h1 := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (ht'bd j).trans (hopt j _ (ht'adm j)))
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at h1
  have hw0 : ∀ e ∈ E, 0 ≤ w e := fun e he => (hU e he).1.trans (hU e he).2
  have hg0 : ∀ e ∈ E, 0 ≤ w e - U e := fun e he => sub_nonneg.mpr (hU e he).2
  -- the weight outside `H` is covered
  have hA : ∑ e ∈ E \ H, w e ≤
      ∑ j, ∑ e ∈ E, (if e ∈ insideEdges E (F j) ∧ e ∉ H then w e else 0) := by
    rw [Finset.sdiff_eq_filter, Finset.sum_filter, Finset.sum_comm]
    refine Finset.sum_le_sum (fun e he => ?_)
    by_cases hH : e ∈ H
    · rw [if_neg (not_not.mpr hH)]
      exact Finset.sum_nonneg (fun j _ => ite_nonneg (hw0 e he) le_rfl)
    · rw [if_pos hH]
      obtain ⟨j0, hj0⟩ := hH1 e he hH
      have hin : e ∈ insideEdges E (F j0) := Finset.mem_filter.mpr ⟨he, hj0⟩
      have := Finset.single_le_sum (f := fun j => if e ∈ insideEdges E (F j) ∧ e ∉ H then w e else 0)
        (fun j _ => ite_nonneg (hw0 e he) le_rfl) (Finset.mem_univ j0)
      refine le_trans (le_of_eq ?_) this
      simp only [hin, hH, not_false_eq_true, and_self, if_true]
  -- the charges sum to at most `2 D_U`
  have hC : ∑ j, (∑ e ∈ E, (if e ∈ insideEdges E (F j) then w e - U e else 0)
      + ∑ p ∈ crossPairs E (F j), (w s(p.1, p.2) - U s(p.1, p.2))) ≤ 2 * ∑ e ∈ E, (w e - U e) := by
    have hCj : ∀ j, ∑ e ∈ E, (if e ∈ insideEdges E (F j) then w e - U e else 0)
        + ∑ p ∈ crossPairs E (F j), (w s(p.1, p.2) - U s(p.1, p.2)) =
        ∑ e ∈ E, ((if e ∈ insideEdges E (F j) then (1 : ℝ) else 0) +
          (if e ∈ (crossPairs E (F j)).image (fun p => s(p.1, p.2)) then 1 else 0)) * (w e - U e) := by
      intro j
      have himg : (crossPairs E (F j)).image (fun p => s(p.1, p.2)) ⊆ E := by
        intro e he
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
        exact (Finset.mem_filter.mp hp).2.1
      have hsimg : ∑ e ∈ (crossPairs E (F j)).image (fun p => s(p.1, p.2)), (w e - U e) =
          ∑ e ∈ E, (if e ∈ (crossPairs E (F j)).image (fun p => s(p.1, p.2)) then w e - U e else 0) := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr himg]
      rw [← Finset.sum_image (f := fun e => w e - U e) (crossPairs_injOn E (F j)), hsimg,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun e _ => ?_)
      split_ifs <;> ring
    simp_rw [hCj]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_le_sum (fun e he => ?_)
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (charge_le_two F hF E e) (hg0 e he)
  linarith

end MTSP813

end ASM2

open scoped Classical

open MetricTSPSublinear in
theorem solution {n : ℕ} {ι : Type*} [Fintype ι] (d : Fin n → Fin n → ℝ) (hsymm : ∀ u v, d u v = d v u)
    (E : Finset (Sym2 (Fin n))) (hT : (SimpleGraph.fromEdgeSet (E : Set (Sym2 (Fin n)))).IsTree)
    (U : Sym2 (Fin n) → ℝ) (hU : ∀ e ∈ E, 0 ≤ U e ∧ U e ≤ DoublingMST.edgeCost d e)
    (hUd : ∀ u v, treeDist E U u v ≤ d u v)
    (F : ι → Finset (Fin n)) (hF : Pairwise fun j k => Disjoint (F j) (F k)) (o : ι → Fin n)
    (H : Finset (Sym2 (Fin n))) (lam r : ℝ) (hlam : 1 ≤ lam)
    (hH1 : ∀ e ∈ E, e ∉ H → ∃ j, ∀ z ∈ e, z ∈ F j)
    (hH2 : ∀ j b c, s(b, c) ∈ E → b ∈ F j → c ∉ F j → pathEdges E b (o j) ⊆ H)
    (hH3 : ∀ j, ∀ v ∈ F j, ∃ a ∈ F j, pathEdges E a (o j) ⊆ H ∧ treeDist E U v a ≤ r)
    (t : ι → Sym2 (Fin n) → ℝ) (ht : ∀ j, IsAdmissibleFragShortening d E (F j) (o j) lam r (t j))
    (hopt : ∀ j t', IsAdmissibleFragShortening d E (F j) (o j) lam r t' → ∑ e ∈ E, t' e ≤ ∑ e ∈ E, t j e) :
    ∑ e ∈ E \ H, DoublingMST.edgeCost d e + (1 - 1 / lam) * ∑ j, ∑ e ∈ E ∩ H, t j e
      - 2 * ∑ e ∈ E, (DoublingMST.edgeCost d e - U e)
      ≤ ∑ j, ∑ e ∈ E, t j e :=
  MTSP813.claim_8_13 d hsymm E hT U hU hUd F hF o H lam r hlam hH1 hH2 hH3 t ht hopt
