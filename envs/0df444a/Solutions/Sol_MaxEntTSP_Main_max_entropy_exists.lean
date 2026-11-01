-- Prove2me | solution 1 for MaxEntTSP.Main.max_entropy_exists
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T08:27:46.274063+00:00
-- url     : https://prove2.me/submissions/131a2dae-0520-4147-b583-7ed8a899619e

import Mathlib
import Definitions.Def_MaxEntTSP_Main_Model
import Theorems.Thm_CombOpt_HeldKarp_forest_polytope
import Theorems.Thm_MaxEntTSP_Main_fact_2_1

open MaxEntTSP.Main MetricTSP Finset

namespace MaxEntAux

variable {m : ℕ}

/-- The graph whose edges are the elements of `E`, each with itself as its pair of ends. -/
def gr (E : Finset (Sym2 (Fin m))) : CombOpt.HeldKarp.Graph (Fin m) E := ⟨fun e => e.val⟩

def emb (E : Finset (Sym2 (Fin m))) : E ↪ Sym2 (Fin m) := Function.Embedding.subtype _

/-- Convert a walk of `fromEdgeSet T` (with `T ⊆ E`) into a walk of `gr E`. -/
def toWalk (E T : Finset (Sym2 (Fin m))) (hT : T ⊆ E) :
    {u v : Fin m} → (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin m)))).Walk u v →
      (gr E).Walk u v
  | _, _, .nil => .nil _
  | u, _, .cons (v := v) h p =>
      .cons ⟨s(u, v), hT (by
        rw [SimpleGraph.fromEdgeSet_adj] at h; exact h.1)⟩ rfl (toWalk E T hT p)

lemma toWalk_edges (E T : Finset (Sym2 (Fin m))) (hT : T ⊆ E) {u v : Fin m}
    (p : (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin m)))).Walk u v) :
    (toWalk E T hT p).edges.map Subtype.val = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [toWalk, CombOpt.HeldKarp.Graph.Walk.edges, List.map_cons,
      SimpleGraph.Walk.edges_cons, ih]

lemma toWalk_support (E T : Finset (Sym2 (Fin m))) (hT : T ⊆ E) {u v : Fin m}
    (p : (SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin m)))).Walk u v) :
    (toWalk E T hT p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [toWalk, CombOpt.HeldKarp.Graph.Walk.support, SimpleGraph.Walk.support_cons, ih]

lemma dropLast_nodup_of_tail {α : Type*} (u : α) (t : List α) (ht : t ≠ [])
    (hlast : t.getLast ht = u) (hnd : t.Nodup) : (u :: t).dropLast.Nodup := by
  have hsplit : t = t.dropLast ++ [u] := by
    conv_lhs => rw [← List.dropLast_append_getLast ht]
    rw [hlast]
  rw [List.dropLast_cons_of_ne_nil ht]
  rw [hsplit] at hnd
  rw [List.nodup_append] at hnd
  refine List.nodup_cons.mpr ⟨?_, hnd.1⟩
  intro hu
  exact hnd.2.2 u hu u (List.mem_singleton_self u) rfl

/-- A forest of `gr E` with `m - 1` edges is a spanning tree. -/
lemma forest_isTree (hm : 1 ≤ m) (E : Finset (Sym2 (Fin m)))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (F : Finset E) (hF : (gr E).IsForest F)
    (hcard : F.card = m - 1) :
    IsSpanningTreeOf E (F.map (emb E)) := by
  classical
  set T := F.map (emb E) with hTdef
  have hTE : T ⊆ E := by
    intro e he
    rw [hTdef, mem_map] at he
    obtain ⟨e', _, rfl⟩ := he
    exact e'.2
  refine ⟨hTE, ?_⟩
  set H := SimpleGraph.fromEdgeSet (T : Set (Sym2 (Fin m))) with hH
  have hedge : H.edgeSet = (T : Set (Sym2 (Fin m))) := by
    rw [hH, SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff, Finset.mem_coe, Set.mem_setOf_eq, and_iff_left_iff_imp]
    intro he
    exact hE e (hTE he)
  -- acyclic
  have hacyc : H.IsAcyclic := by
    intro v c hc
    apply hF
    refine ⟨v, toWalk E T hTE c, ⟨?_, ?_, ?_⟩, ?_⟩
    · have := hc.edges_nodup
      rw [← toWalk_edges E T hTE c] at this
      exact List.Nodup.of_map _ this
    · rw [toWalk_support]
      have hnn : c.support.tail ≠ [] := by
        intro h
        have h1 := congrArg List.length h
        rw [List.length_tail, SimpleGraph.Walk.length_support] at h1
        have := hc.three_le_length
        simp only [List.length_nil] at h1; omega
      have hsup : c.support = v :: c.support.tail := by
        conv_lhs => rw [← List.cons_head_tail (SimpleGraph.Walk.support_ne_nil c)]
        rw [SimpleGraph.Walk.head_support]
      rw [hsup]
      apply dropLast_nodup_of_tail v _ hnn _ hc.support_nodup
      have h1 := SimpleGraph.Walk.getLast_support c
      rw [← List.getLast_cons hnn (a := v)]
      simp only [← hsup, h1]
    · have := hc.three_le_length
      have hl : (toWalk E T hTE c).edges.length = c.length := by
        rw [← List.length_map (f := Subtype.val), toWalk_edges, SimpleGraph.Walk.length_edges]
      omega
    · intro e he
      have : e.val ∈ c.edges := by
        rw [← toWalk_edges E T hTE c]; exact List.mem_map_of_mem he
      have h2 := c.edges_subset_edgeSet this
      rw [hedge] at h2
      rw [Finset.mem_coe, hTdef, mem_map] at h2
      obtain ⟨e', he', hee⟩ := h2
      have : e' = e := Subtype.ext hee
      rw [← this]; exact he'
  -- extend to a maximal acyclic graph, which is a tree
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  obtain ⟨H', hle, hmax⟩ := SimpleGraph.exists_maximal_isAcyclic_of_le_isAcyclic
    (G := (⊤ : SimpleGraph (Fin m))) le_top hacyc
  have hmax' : Maximal SimpleGraph.IsAcyclic H' := by
    refine ⟨hmax.1.2, fun K hK hle' => hmax.2 ⟨le_top, hK⟩ hle'⟩
  have htree : H'.IsTree := SimpleGraph.maximal_isAcyclic_iff_isTree.mp hmax'
  have hcardH' := htree.card_edgeFinset
  simp only [Fintype.card_fin] at hcardH'
  have hcardH : H.edgeFinset.card = m - 1 := by
    have : H.edgeFinset = T := by
      ext e; rw [SimpleGraph.mem_edgeFinset, hedge, Finset.mem_coe]
    rw [this, hTdef, card_map, hcard]
  have hsub : H.edgeFinset ⊆ H'.edgeFinset := SimpleGraph.edgeFinset_mono hle
  have heq : H.edgeFinset = H'.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have : H = H' := by
    rw [SimpleGraph.edgeFinset_inj] at heq; exact heq
  rw [this]; exact htree

/-- Compactness: if some tree law with the given marginals exists, an entropy maximizer exists. -/
lemma exists_maxEnt (E : Finset (Sym2 (Fin m))) (x : Fin m → Fin m → ℝ)
    (hne : ∃ ν, IsTreeDistribution E x ν) : ∃ μ, IsMaxEntropy E x μ := by
  classical
  set K := {μ : Finset (Sym2 (Fin m)) → ℝ | IsTreeDistribution E x μ} with hK
  have hclosed : IsClosed K := by
    have : K = (⋂ T, {μ : Finset (Sym2 (Fin m)) → ℝ | 0 ≤ μ T}) ∩
        (⋂ T, {μ : Finset (Sym2 (Fin m)) → ℝ | IsSpanningTreeOf E T ∨ μ T = 0}) ∩
        {μ | (∑ T, μ T) = 1} ∩
        (⋂ e ∈ E, {μ : Finset (Sym2 (Fin m)) → ℝ |
          (∑ T ∈ (univ.filter (fun T => e ∈ T)), μ T) = pairCost x e}) := by
      ext μ
      simp only [hK, IsTreeDistribution, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2, h3, h4⟩
        refine ⟨⟨⟨h1, fun T => ?_⟩, h3⟩, h4⟩
        by_cases h : μ T = 0
        · exact Or.inr h
        · exact Or.inl (h2 T h)
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
        refine ⟨h1, fun T hT => ?_, h3, h4⟩
        rcases h2 T with h | h
        · exact h
        · exact absurd h hT
    rw [this]
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · exact isClosed_iInter (fun T => isClosed_le continuous_const (continuous_apply T))
    · refine isClosed_iInter (fun T => ?_)
      by_cases h : IsSpanningTreeOf E T
      · simp only [h, true_or, Set.setOf_true]; exact isClosed_univ
      · simp only [h, false_or]
        exact isClosed_eq (continuous_apply T) continuous_const
    · exact isClosed_eq (continuous_finset_sum _ (fun T _ => continuous_apply T))
        continuous_const
    · exact isClosed_biInter (fun e _ => isClosed_eq
        (continuous_finset_sum _ (fun T _ => continuous_apply T)) continuous_const)
  have hsub : K ⊆ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
    intro μ hμ T _
    refine ⟨hμ.1 T, ?_⟩
    rw [← hμ.2.2.1]
    exact Finset.single_le_sum (f := μ) (fun T _ => hμ.1 T) (mem_univ T)
  have hcpt : IsCompact K :=
    (isCompact_univ_pi (fun _ => isCompact_Icc)).of_isClosed_subset hclosed hsub
  have hcont : Continuous (fun μ : Finset (Sym2 (Fin m)) → ℝ => entropy μ) := by
    unfold entropy
    exact continuous_finset_sum _ (fun T _ => Real.continuous_negMulLog.comp (continuous_apply T))
  obtain ⟨μ, hμK, hmax⟩ := hcpt.exists_isMaxOn hne hcont.continuousOn
  exact ⟨μ, hμK, fun ν hν => hmax hν⟩

end MaxEntAux

open MaxEntAux in
theorem solution (m : ℕ) (hm : 3 ≤ m)
    (x : Fin m → Fin m → ℝ) (hx : IsHeldKarp x)
    (a b : Fin m) (hab : a ≠ b) (he0 : x a b = 1) :
    ∃ μ : Finset (Sym2 (Fin m)) → ℝ, IsMaxEntropy (lpSupport x a b) x μ := by
  classical
  apply exists_maxEnt
  obtain ⟨hmass, hint, hnn⟩ := fact_2_1 m hm x hx a b hab he0
  set E := lpSupport x a b with hEdef
  have hEd : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he; rw [hEdef, lpSupport, mem_filter] at he; exact he.2.1
  let G := gr E
  let wv : E → ℝ := fun e => pairCost x e.val
  -- edges of `γ(S)` are the internal edges of `E`
  have hgamma : ∀ S : Finset (Fin m), (G.gamma S).map (emb E) = internalEdges E S := by
    intro S
    ext e
    simp only [mem_map, CombOpt.HeldKarp.Graph.gamma, mem_filter, mem_univ, true_and,
      internalEdges, emb, Function.Embedding.subtype_apply]
    constructor
    · rintro ⟨e', he', rfl⟩
      refine ⟨e'.2, ?_⟩
      have he'' : ∀ a ∈ e'.val, a ∈ S := he'
      induction h : e'.val using Sym2.ind with
      | h i j =>
        rw [h] at he''
        exact ⟨i, j, rfl, he'' i (Sym2.mem_mk_left i j), he'' j (Sym2.mem_mk_right i j)⟩
    · rintro ⟨he, i, j, rfl, hi, hj⟩
      refine ⟨⟨s(i, j), he⟩, ?_, rfl⟩
      show ∀ a ∈ s(i, j), a ∈ S
      intro c hc
      rcases Sym2.mem_iff.mp hc with rfl | rfl
      · exact hi
      · exact hj
  have hsumgamma : ∀ (S : Finset (Fin m)) (f : Sym2 (Fin m) → ℝ),
      (∑ e ∈ G.gamma S, f e.val) = ∑ e ∈ internalEdges E S, f e := by
    intro S f
    rw [← hgamma S, sum_map]; rfl
  -- `wv` lies in the forest polytope
  have hpoly : wv ∈ convexHull ℝ {y : E → ℝ | ∃ F : Finset E, G.IsForest F ∧
      y = fun e => if e ∈ F then 1 else 0} := by
    rw [CombOpt.HeldKarp.forest_polytope G]
    refine ⟨fun S hS => ?_, fun e => hnn e.val e.2⟩
    rw [hsumgamma S (pairCost x)]
    exact hint S hS
  rw [_root_.convexHull_eq] at hpoly
  obtain ⟨ι, t, w, z, hw0, hw1, hz, hcm⟩ := hpoly
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw1] at hcm
  have hzF : ∀ i ∈ t, ∃ F : Finset E, G.IsForest F ∧ z i = fun e => if e ∈ F then 1 else 0 :=
    fun i hi => hz i hi
  let Fi : ι → Finset E := fun i => if h : i ∈ t then Classical.choose (hzF i h) else ∅
  have hFi : ∀ i ∈ t, G.IsForest (Fi i) ∧ z i = fun e => if e ∈ Fi i then 1 else 0 := by
    intro i hi
    simp only [Fi, dif_pos hi]
    exact Classical.choose_spec (hzF i hi)
  -- every forest has at most `m - 1` edges (polytope inequality for `S = V`)
  have hcard_le : ∀ i ∈ t, ((Fi i).card : ℝ) ≤ (m : ℝ) - 1 := by
    intro i hi
    have hmem : z i ∈ convexHull ℝ {y : E → ℝ | ∃ F : Finset E, G.IsForest F ∧
        y = fun e => if e ∈ F then 1 else 0} := subset_convexHull ℝ _ (hz i hi)
    rw [CombOpt.HeldKarp.forest_polytope G] at hmem
    have h := hmem.1 univ ⟨⟨0, by omega⟩, mem_univ _⟩
    have hg : G.gamma univ = univ := by
      ext e; simp [CombOpt.HeldKarp.Graph.gamma]
    rw [hg, (hFi i hi).2] at h
    simp only [sum_boole, filter_mem_eq_inter, univ_inter, card_univ, Fintype.card_fin] at h
    exact h
  -- total mass identity
  have hwv : ∀ e : E, wv e = ∑ i ∈ t, w i * z i e := by
    intro e
    rw [← hcm, Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
  have htotal : (∑ i ∈ t, w i * ((Fi i).card : ℝ)) = (m : ℝ) - 1 := by
    have h1 : (∑ e : E, wv e) = (m : ℝ) - 1 := by
      rw [← hmass]; unfold edgeMass
      exact Finset.sum_coe_sort E (pairCost x)
    rw [← h1]
    simp_rw [hwv]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.mul_sum, (hFi i hi).2]
    simp only [sum_boole, filter_mem_eq_inter, univ_inter]
  have hzero : ∀ i ∈ t, w i * ((m : ℝ) - 1 - (Fi i).card) = 0 := by
    have hs : (∑ i ∈ t, w i * ((m : ℝ) - 1 - (Fi i).card)) = 0 := by
      simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, htotal]; ring
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi =>
      mul_nonneg (hw0 i hi) (by linarith [hcard_le i hi]))).mp hs
  -- the tree law
  let g : ι → Finset (Sym2 (Fin m)) := fun i => (Fi i).map (emb E)
  refine ⟨fun T => ∑ i ∈ t with g i = T, w i, ?_, ?_, ?_, ?_⟩
  · intro T
    exact Finset.sum_nonneg (fun i hi => hw0 i (mem_filter.mp hi).1)
  · intro T hT
    obtain ⟨i, hi, hwi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hT
    rw [mem_filter] at hi
    rw [← hi.2]
    have hc : ((Fi i).card : ℝ) = (m : ℝ) - 1 := by
      have := hzero i hi.1
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hwi
      · linarith
    apply forest_isTree (by omega) E hEd (Fi i) (hFi i hi.1).1
    have : ((Fi i).card : ℝ) = ((m - 1 : ℕ) : ℝ) := by
      rw [hc, Nat.cast_sub (by omega)]; simp
    exact_mod_cast this
  · rw [Finset.sum_fiberwise]; exact hw1
  · intro e he
    rw [Finset.sum_filter]
    have : ∀ T : Finset (Sym2 (Fin m)), (if e ∈ T then ∑ i ∈ t with g i = T, w i else 0) =
        ∑ i ∈ t with g i = T, (if e ∈ g i then w i else 0) := by
      intro T
      split_ifs with h
      · apply Finset.sum_congr rfl
        intro i hi; rw [(mem_filter.mp hi).2, if_pos h]
      · symm; apply Finset.sum_eq_zero
        intro i hi; rw [(mem_filter.mp hi).2, if_neg h]
    simp_rw [this]
    rw [Finset.sum_fiberwise]
    have hw' := hwv ⟨e, he⟩
    simp only [wv] at hw'
    rw [hw']
    apply Finset.sum_congr rfl
    intro i hi
    rw [(hFi i hi).2]
    have : e ∈ g i ↔ (⟨e, he⟩ : E) ∈ Fi i := by
      simp only [g, mem_map, emb, Function.Embedding.subtype_apply]
      constructor
      · rintro ⟨e', he', rfl⟩; exact he'
      · intro h; exact ⟨_, h, rfl⟩
    by_cases h : (⟨e, he⟩ : E) ∈ Fi i
    · rw [if_pos (this.mpr h)]; simp [h]
    · rw [if_neg (fun h' => h (this.mp h'))]; simp [h]
