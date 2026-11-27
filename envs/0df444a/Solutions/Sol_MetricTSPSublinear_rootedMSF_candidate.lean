-- Prove2me | solution 1 for MetricTSPSublinear.rootedMSF_candidate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T04:31:44.780268+00:00
-- url     : https://prove2.me/submissions/cb02b473-5195-4ecd-86e4-68a320c6b648

import Mathlib
import Definitions.Def_DoublingMST_completeGraph
import Definitions.Def_CombOpt_SpanningTree_Graph_IsForest
import Definitions.Def_DoublingMST_treeWeight
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_MetricTSPSublinear_treeDist
import Definitions.Def_MetricTSPSublinear_IsRootedMSF


/-!
# Rooted minimum spanning forests

Azarmehr–Behnezhad, *Metric TSP in Sublinear Time*, arXiv:2611.04283, p.10: the rooted MSF is a
minimum-weight forest each of whose components contains exactly one root. We prove existence, the
exchange (cut) property, the path bound of Claim 9.5 and the candidate-edge property of Claim 9.3.
-/

namespace MTSPRF
open Finset CombOpt.SpanningTree MetricTSPSublinear

variable {n : ℕ}
/-! ### Bridge to Mathlib simple graphs -/

/-- The Mathlib simple graph of an edge set (loops dropped). -/
abbrev gr (F : Finset (Sym2 (Fin n))) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 (Fin n)))

/-- A Mathlib walk as a walk of the complete graph. -/
noncomputable def ofWalk {G : SimpleGraph (Fin n)} :
    {u v : Fin n} → G.Walk u v → (DoublingMST.completeGraph n).Walk u v
  | _, _, SimpleGraph.Walk.nil => Graph.Walk.nil _
  | u, _, SimpleGraph.Walk.cons (v := w) _ p => Graph.Walk.cons s(u, w) rfl (ofWalk p)

lemma ofWalk_edges {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v) :
    (ofWalk p).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [ofWalk, Graph.Walk.edges, SimpleGraph.Walk.edges_cons, ih]

lemma ofWalk_support {G : SimpleGraph (Fin n)} {u v : Fin n} (p : G.Walk u v) :
    (ofWalk p).support = p.support := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [ofWalk, Graph.Walk.support, SimpleGraph.Walk.support_cons, ih]

/-- A walk of the complete graph whose edges are edges of `G`, as a Mathlib walk of `G`. -/
noncomputable def toWalk (G : SimpleGraph (Fin n)) :
    {u v : Fin n} → (p : (DoublingMST.completeGraph n).Walk u v) →
      (∀ e ∈ p.edges, e ∈ G.edgeSet) → G.Walk u v
  | _, _, Graph.Walk.nil _, _ => SimpleGraph.Walk.nil
  | _, _, Graph.Walk.cons e h p, hp =>
      SimpleGraph.Walk.cons
        (by
          have he : e ∈ G.edgeSet := hp e (by simp [Graph.Walk.edges])
          have h' : e = _ := h
          rw [h'] at he
          exact (SimpleGraph.mem_edgeSet G).mp he)
        (toWalk G p (fun e' he' => hp e' (by simp [Graph.Walk.edges, he'])))

lemma toWalk_edges (G : SimpleGraph (Fin n)) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    (toWalk G p hp).edges = p.edges := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    have h' : e = _ := h
    rw [toWalk, SimpleGraph.Walk.edges_cons, Graph.Walk.edges, ih, h']

lemma toWalk_support (G : SimpleGraph (Fin n)) {u v : Fin n}
    (p : (DoublingMST.completeGraph n).Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    (toWalk G p hp).support = p.support := by
  induction p with
  | nil => rfl
  | cons e h p ih =>
    rw [toWalk, SimpleGraph.Walk.support_cons, Graph.Walk.support, ih]

lemma tail_nodup_of_dropLast_nodup {α : Type*} (v : α) (t : List α) (ht : t ≠ [])
    (hlast : t.getLast ht = v) (h : (v :: t).dropLast.Nodup) : t.Nodup := by
  rw [List.dropLast_cons_of_ne_nil ht] at h
  have ht' : t = t.dropLast ++ [v] := by
    conv_lhs => rw [← List.dropLast_append_getLast ht]
    rw [hlast]
  rw [ht']
  exact (List.perm_append_singleton v t.dropLast).nodup_iff.mpr h

lemma mem_of_mem_edgeSet {F : Finset (Sym2 (Fin n))} {e : Sym2 (Fin n)}
    (h : e ∈ (gr F).edgeSet) : e ∈ F := by
  rw [SimpleGraph.edgeSet_fromEdgeSet] at h
  exact h.1

lemma reachIn_iff {F : Finset (Sym2 (Fin n))} {u v : Fin n} :
    reachIn F u v ↔ (gr F).Reachable u v := by
  constructor
  · rintro ⟨p, hp⟩
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b c e h p ih =>
      have h' : e = s(a, b) := h
      have heF : e ∈ F := hp e (by simp [Graph.Walk.edges])
      have hrest := ih (fun e' he' => hp e' (by simp [Graph.Walk.edges, he']))
      by_cases hab : a = b
      · subst hab; exact hrest
      · refine SimpleGraph.Reachable.trans ?_ hrest
        apply SimpleGraph.Adj.reachable
        rw [SimpleGraph.fromEdgeSet_adj]
        exact ⟨by rw [← h']; exact heF, hab⟩
  · rintro ⟨q⟩
    refine ⟨ofWalk q, fun e he => ?_⟩
    rw [ofWalk_edges] at he
    exact mem_of_mem_edgeSet (q.edges_subset_edgeSet he)

lemma reachIn_mono {F1 F2 : Finset (Sym2 (Fin n))} (h : F1 ⊆ F2) {u v : Fin n}
    (hr : reachIn F1 u v) : reachIn F2 u v := by
  obtain ⟨p, hp⟩ := hr
  exact ⟨p, fun e he => h (hp e he)⟩

lemma gr_mono {F1 F2 : Finset (Sym2 (Fin n))} (h : F1 ⊆ F2) : gr F1 ≤ gr F2 :=
  SimpleGraph.fromEdgeSet_mono (by exact_mod_cast h)

lemma gr_insert (F : Finset (Sym2 (Fin n))) (a b : Fin n) :
    gr (insert s(a, b) F) = gr F ⊔ SimpleGraph.edge a b := by
  ext x y
  simp only [SimpleGraph.fromEdgeSet_adj, SimpleGraph.sup_adj, SimpleGraph.edge_adj,
    Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Sym2.eq_iff]
  tauto

/-- A forest contains no loop. -/
lemma not_isDiag_of_isForest {T : Finset (Sym2 (Fin n))}
    (hT : (DoublingMST.completeGraph n).IsForest T) {e : Sym2 (Fin n)} (he : e ∈ T) :
    ¬ e.IsDiag := by
  intro hdiag
  induction e with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hdiag
    subst hdiag
    apply hT
    refine ⟨a, Graph.Walk.cons s(a, a) rfl (Graph.Walk.nil a), ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [Graph.Walk.edges]
      · simp [Graph.Walk.support]
      · simp [Graph.Walk.edges]
    · intro e he
      simp [Graph.Walk.edges] at he
      rw [he]; exact he ▸ ‹s(a, a) ∈ T›

lemma isAcyclic_of_isForest {F : Finset (Sym2 (Fin n))}
    (hF : (DoublingMST.completeGraph n).IsForest F) : (gr F).IsAcyclic := by
  intro v c hc
  apply hF
  refine ⟨v, ofWalk c, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [ofWalk_edges]; exact hc.edges_nodup
  · rw [ofWalk_support]; exact hc.nodup_dropLast_support
  · rw [ofWalk_edges, SimpleGraph.Walk.length_edges]
    have := hc.three_le_length
    omega
  · intro e he
    rw [ofWalk_edges] at he
    exact mem_of_mem_edgeSet (c.edges_subset_edgeSet he)

lemma isForest_of_isAcyclic {F : Finset (Sym2 (Fin n))} (hdiag : ∀ e ∈ F, ¬ e.IsDiag)
    (hac : (gr F).IsAcyclic) : (DoublingMST.completeGraph n).IsForest F := by
  rintro ⟨v, p, hcirc, hsub⟩
  have hp : ∀ e ∈ p.edges, e ∈ (gr F).edgeSet := fun e he => by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact ⟨hsub e he, hdiag e (hsub e he)⟩
  obtain ⟨q, hqe, hqs⟩ : ∃ q : (gr F).Walk v v, q.edges = p.edges ∧ q.support = p.support :=
    ⟨toWalk _ p hp, toWalk_edges _ p hp, toWalk_support _ p hp⟩
  apply hac q
  rw [SimpleGraph.Walk.isCycle_def]
  obtain ⟨hnd, hdl, hlen⟩ := hcirc
  have hlen' : 1 ≤ q.length := by rw [← SimpleGraph.Walk.length_edges, hqe]; exact hlen
  have hne : q ≠ SimpleGraph.Walk.nil := by
    intro h
    rw [h] at hlen'
    simp at hlen'
  refine ⟨?_, hne, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def, hqe]; exact hnd
  · have hsupp : q.support = v :: q.support.tail := (q.cons_tail_support).symm
    have htne : q.support.tail ≠ [] := by
      intro h
      have hl := q.length_support
      rw [hsupp, h] at hl
      simp only [List.length_cons, List.length_nil] at hl
      omega
    have hgl : ∀ (L : List (Fin n)) (hL : L ≠ []) (ht : L.tail ≠ []),
        L.getLast hL = L.tail.getLast ht := by
      intro L hL ht
      cases L with
      | nil => exact absurd rfl hL
      | cons a t => exact List.getLast_cons ht
    apply tail_nodup_of_dropLast_nodup v q.support.tail htne
    · rw [← hgl q.support (by simp) htne]
      exact q.getLast_support
    · rw [← hsupp, hqs]; exact hdl

/-- Deleting an edge `s(a, b)` of a forest disconnects `a` from `b`. -/
lemma not_reach_erase {F : Finset (Sym2 (Fin n))}
    (hF : (DoublingMST.completeGraph n).IsForest F) {a b : Fin n} (he : s(a, b) ∈ F) :
    ¬ (gr (F.erase s(a, b))).Reachable a b := by
  have hac := isAcyclic_of_isForest hF
  have hab : a ≠ b := fun h => not_isDiag_of_isForest hF he (by simp [h])
  have hadj : (gr F).Adj a b := by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨he, hab⟩
  have hbr := SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hac hadj
  rw [SimpleGraph.isBridge_iff] at hbr
  have : gr (F.erase s(a, b)) = (gr F).deleteEdges {s(a, b)} := by
    ext x y
    simp only [SimpleGraph.fromEdgeSet_adj, SimpleGraph.deleteEdges_adj, Finset.coe_erase,
      Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff]
    tauto
  rw [this]; exact hbr

/-- Reachability after adding one edge `s(a, b)`. -/
lemma reach_split {F1 F2 : Finset (Sym2 (Fin n))} {a b : Fin n}
    (hsub : ∀ e ∈ F2, e ∈ F1 ∨ e = s(a, b)) {x t : Fin n} (h : (gr F2).Reachable x t) :
    (gr F1).Reachable x t ∨ ((gr F1).Reachable x a ∧ (gr F1).Reachable b t) ∨
      ((gr F1).Reachable x b ∧ (gr F1).Reachable a t) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons x y t hxy p ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hxy
    rcases hsub _ hxy.1 with h1 | h1
    · have hr : (gr F1).Reachable x y :=
        SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨h1, hxy.2⟩)
      rcases ih with h | ⟨h2, h3⟩ | ⟨h2, h3⟩
      · exact Or.inl (hr.trans h)
      · exact Or.inr (Or.inl ⟨hr.trans h2, h3⟩)
      · exact Or.inr (Or.inr ⟨hr.trans h2, h3⟩)
    · rcases Sym2.eq_iff.mp h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases ih with h | ⟨h2, h3⟩ | ⟨h2, h3⟩
        · exact Or.inr (Or.inl ⟨SimpleGraph.Reachable.refl _, h⟩)
        · exact Or.inl (h2.symm.trans h3)
        · exact Or.inl h3
      · rcases ih with h | ⟨h2, h3⟩ | ⟨h2, h3⟩
        · exact Or.inr (Or.inr ⟨SimpleGraph.Reachable.refl _, h⟩)
        · exact Or.inl h3
        · exact Or.inl (h2.symm.trans h3)

/-! ### Roots -/

section Roots
variable {R : Finset (Fin n)} {F : Finset (Sym2 (Fin n))}

lemma exists_root (hF : IsRootedSpanningForest R F) (v : Fin n) :
    ∃ r ∈ R, (gr F).Reachable v r := by
  obtain ⟨r, ⟨hr, h⟩, _⟩ := hF.2 v
  exact ⟨r, hr, reachIn_iff.mp h⟩

lemma root_unique (hF : IsRootedSpanningForest R F) {v r1 r2 : Fin n} (h1 : r1 ∈ R)
    (h1' : (gr F).Reachable v r1) (h2 : r2 ∈ R) (h2' : (gr F).Reachable v r2) : r1 = r2 :=
  (hF.2 v).unique ⟨h1, reachIn_iff.mpr h1'⟩ ⟨h2, reachIn_iff.mpr h2'⟩

lemma split_erase (a b : Fin n) : ∀ e ∈ F, e ∈ F.erase s(a, b) ∨ e = s(a, b) := by
  intro e he
  by_cases h : e = s(a, b)
  · exact Or.inr h
  · exact Or.inl (Finset.mem_erase.mpr ⟨h, he⟩)

/-- Removing an edge `s(a, b)` of a rooted spanning forest: one of `a`, `b` loses its root. -/
lemma rootless_or (hF : IsRootedSpanningForest R F) {a b : Fin n} (he : s(a, b) ∈ F) :
    (∀ r ∈ R, ¬ (gr (F.erase s(a, b))).Reachable a r) ∨
      (∀ r ∈ R, ¬ (gr (F.erase s(a, b))).Reachable b r) := by
  by_contra h
  push Not at h
  obtain ⟨⟨r1, hr1, h1⟩, ⟨r2, hr2, h2⟩⟩ := h
  have hsub := gr_mono (Finset.erase_subset s(a, b) F)
  have hab : a ≠ b := fun h => not_isDiag_of_isForest hF.1 he (by simp [h])
  have hadj : (gr F).Reachable a b :=
    SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨he, hab⟩)
  have : r1 = r2 := root_unique hF hr1 (h1.mono hsub) hr2 (hadj.trans (h2.mono hsub))
  subst this
  exact not_reach_erase hF.1 he (h1.trans h2.symm)

/-- After removing `s(a, b)`, all rootless vertices lie in one component. -/
lemma rootless_conn (hF : IsRootedSpanningForest R F) {a b : Fin n} (he : s(a, b) ∈ F)
    {v w : Fin n} (hv : ∀ r ∈ R, ¬ (gr (F.erase s(a, b))).Reachable v r)
    (hw : ∀ r ∈ R, ¬ (gr (F.erase s(a, b))).Reachable w r) :
    (gr (F.erase s(a, b))).Reachable v w := by
  have key : ∀ x, (∀ r ∈ R, ¬ (gr (F.erase s(a, b))).Reachable x r) →
      ((gr (F.erase s(a, b))).Reachable x a ∧ ∃ r ∈ R, (gr (F.erase s(a, b))).Reachable b r) ∨
      ((gr (F.erase s(a, b))).Reachable x b ∧ ∃ r ∈ R, (gr (F.erase s(a, b))).Reachable a r) := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := exists_root hF x
    rcases reach_split (split_erase a b) hxr with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact absurd h (hx r hr)
    · exact Or.inl ⟨h1, r, hr, h2⟩
    · exact Or.inr ⟨h1, r, hr, h2⟩
  have hboth : ¬ ((∃ r ∈ R, (gr (F.erase s(a, b))).Reachable b r) ∧
      ∃ r ∈ R, (gr (F.erase s(a, b))).Reachable a r) := by
    rintro ⟨⟨r1, hr1, h1⟩, ⟨r2, hr2, h2⟩⟩
    rcases rootless_or hF he with h | h
    · exact h r2 hr2 h2
    · exact h r1 hr1 h1
  rcases key v hv with ⟨hva, hb⟩ | ⟨hvb, ha⟩ <;>
    rcases key w hw with ⟨hwa, hb'⟩ | ⟨hwb, ha'⟩
  · exact hva.trans hwa.symm
  · exact absurd ⟨hb, ha'⟩ hboth
  · exact absurd ⟨hb', ha⟩ hboth
  · exact hvb.trans hwb.symm

/-- The exchange: reconnecting the rootless side by `s(w, y)` gives a rooted spanning forest. -/
lemma exchange (hF : IsRootedSpanningForest R F) {a b : Fin n} (he : s(a, b) ∈ F)
    {w y : Fin n} (hw : ∀ r ∈ R, ¬ (gr (F.erase s(a, b))).Reachable w r)
    (hwy : ¬ (gr (F.erase s(a, b))).Reachable w y) :
    IsRootedSpanningForest R (insert s(w, y) (F.erase s(a, b))) := by
  set H := gr (F.erase s(a, b)) with hH
  have hHF : H ≤ gr F := gr_mono (Finset.erase_subset _ _)
  have hHF' : H ≤ gr (insert s(w, y) (F.erase s(a, b))) := gr_mono (Finset.subset_insert _ _)
  have hwy' : w ≠ y := fun h => hwy (h ▸ SimpleGraph.Reachable.refl _)
  have hadj : (gr (insert s(w, y) (F.erase s(a, b)))).Adj w y := by
    rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp, hwy'⟩
  -- `y` has a root in `H`
  have hy : ∃ r ∈ R, H.Reachable y r := by
    by_contra h
    push Not at h
    exact hwy (rootless_conn hF he hw h)
  obtain ⟨ry, hry, hyr⟩ := hy
  refine ⟨?_, fun v => ?_⟩
  · apply isForest_of_isAcyclic
    · intro e' he'
      rcases Finset.mem_insert.mp he' with h | h
      · rw [h, Sym2.mk_isDiag_iff]; exact hwy'
      · exact not_isDiag_of_isForest hF.1 (Finset.mem_of_mem_erase h)
    · rw [gr_insert]
      exact ((isAcyclic_of_isForest hF.1).anti hHF).sup_edge_of_not_reachable hwy
  · set F' := insert s(w, y) (F.erase s(a, b)) with hF'
    have hsplit : ∀ r ∈ R, reachIn F' v r →
        H.Reachable v r ∨ (H.Reachable v w ∧ H.Reachable y r) := by
      intro r hr h
      have hsub : ∀ e ∈ F', e ∈ F.erase s(a, b) ∨ e = s(w, y) := by
        intro e he'
        rcases Finset.mem_insert.mp he' with h | h
        · exact Or.inr h
        · exact Or.inl h
      rcases reach_split hsub (reachIn_iff.mp h) with h | h | ⟨_, h2⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h2 (hw r hr)
    have huniq : ∀ r1 r2, r1 ∈ R → reachIn F' v r1 → r2 ∈ R → reachIn F' v r2 → r1 = r2 := by
      intro r1 r2 hr1 h1 hr2 h2
      rcases hsplit r1 hr1 h1 with h1 | ⟨h1w, h1y⟩ <;>
        rcases hsplit r2 hr2 h2 with h2 | ⟨h2w, h2y⟩
      · exact root_unique hF hr1 (h1.mono hHF) hr2 (h2.mono hHF)
      · exact absurd (h2w.symm.trans h1) (hw r1 hr1)
      · exact absurd (h1w.symm.trans h2) (hw r2 hr2)
      · exact root_unique hF hr1 (h1y.mono hHF) hr2 (h2y.mono hHF)
    have hex : ∃ r, r ∈ R ∧ reachIn F' v r := by
      obtain ⟨rv, hrv, hvr⟩ := exists_root hF v
      by_cases hH' : H.Reachable v rv
      · exact ⟨rv, hrv, reachIn_iff.mpr (hH'.mono hHF')⟩
      · have hvroot : ∀ r ∈ R, ¬ H.Reachable v r := by
          intro r hr hvr'
          have := root_unique hF hr (hvr'.mono hHF) hrv hvr
          subst this; exact hH' hvr'
        exact ⟨ry, hry, reachIn_iff.mpr (((rootless_conn hF he hvroot hw).mono hHF').trans
          (hadj.reachable.trans (hyr.mono hHF')))⟩
    obtain ⟨r, hr, hvr⟩ := hex
    exact ⟨r, ⟨hr, hvr⟩, fun r' ⟨hr', h'⟩ => huniq _ _ hr' h' hr hvr⟩

end Roots

/-! ### Existence -/

/-- Joining two distinct roots `r0`, `v` by an edge; `v` stops being a root. -/
lemma merge {Q : Finset (Fin n)} {F : Finset (Sym2 (Fin n))} (hF : IsRootedSpanningForest Q F)
    {v r0 : Fin n} (hv : v ∈ Q) (hr : r0 ∈ Q) (hne : v ≠ r0) :
    IsRootedSpanningForest (Q.erase v) (insert s(r0, v) F) := by
  have hsub : F ⊆ insert s(r0, v) F := Finset.subset_insert _ _
  have hnr : ¬ (gr F).Reachable r0 v := fun h =>
    hne (root_unique hF hr (SimpleGraph.Reachable.refl _) hv h).symm
  have hadj : (gr (insert s(r0, v) F)).Adj v r0 := by
    rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp [Sym2.eq_swap], hne⟩
  refine ⟨?_, fun x => ?_⟩
  · apply isForest_of_isAcyclic
    · intro e he
      rcases Finset.mem_insert.mp he with h | h
      · rw [h, Sym2.mk_isDiag_iff]; exact fun h' => hne h'.symm
      · exact not_isDiag_of_isForest hF.1 h
    · rw [gr_insert]
      exact (isAcyclic_of_isForest hF.1).sup_edge_of_not_reachable hnr
  · have hsplit : ∀ t ∈ Q.erase v, reachIn (insert s(r0, v) F) x t →
        (gr F).Reachable x t ∨ ((gr F).Reachable x v ∧ t = r0) := by
      intro t ht h
      have hsub' : ∀ e ∈ insert s(r0, v) F, e ∈ F ∨ e = s(r0, v) := by
        intro e he
        rcases Finset.mem_insert.mp he with h | h
        · exact Or.inr h
        · exact Or.inl h
      obtain ⟨htv, htQ⟩ := Finset.mem_erase.mp ht
      rcases reach_split hsub' (reachIn_iff.mp h) with h | ⟨_, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h
      · exact absurd (root_unique hF hv (SimpleGraph.Reachable.refl _) htQ h2).symm htv
      · exact Or.inr ⟨h1, (root_unique hF hr (SimpleGraph.Reachable.refl _) htQ h2).symm⟩
    have huniq : ∀ t1 t2, t1 ∈ Q.erase v → reachIn (insert s(r0, v) F) x t1 →
        t2 ∈ Q.erase v → reachIn (insert s(r0, v) F) x t2 → t1 = t2 := by
      intro t1 t2 ht1 h1 ht2 h2
      have ht1' := Finset.mem_erase.mp ht1
      have ht2' := Finset.mem_erase.mp ht2
      rcases hsplit t1 ht1 h1 with g1 | ⟨g1v, e1⟩ <;>
        rcases hsplit t2 ht2 h2 with g2 | ⟨g2v, e2⟩
      · exact root_unique hF ht1'.2 g1 ht2'.2 g2
      · exact absurd (root_unique hF ht1'.2 g1 hv g2v) ht1'.1
      · exact absurd (root_unique hF ht2'.2 g2 hv g1v) ht2'.1
      · rw [e1, e2]
    have hex : ∃ t, t ∈ Q.erase v ∧ reachIn (insert s(r0, v) F) x t := by
      obtain ⟨t, ht, hxt⟩ := exists_root hF x
      by_cases htv : t = v
      · subst htv
        exact ⟨r0, Finset.mem_erase.mpr ⟨hne.symm, hr⟩,
          reachIn_iff.mpr ((hxt.mono (gr_mono hsub)).trans hadj.reachable)⟩
      · exact ⟨t, Finset.mem_erase.mpr ⟨htv, ht⟩, reachIn_iff.mpr (hxt.mono (gr_mono hsub))⟩
    obtain ⟨t, ht, hxt⟩ := hex
    exact ⟨t, ⟨ht, hxt⟩, fun t' ⟨ht', h'⟩ => huniq _ _ ht' h' ht hxt⟩

lemma isRootedSpanningForest_empty : IsRootedSpanningForest (univ : Finset (Fin n)) ∅ := by
  refine ⟨?_, fun v => ⟨v, ⟨mem_univ _, reachIn_iff.mpr (SimpleGraph.Reachable.refl _)⟩, ?_⟩⟩
  · rintro ⟨v, p, ⟨_, _, hlen⟩, hsub⟩
    obtain ⟨e, he⟩ := List.exists_mem_of_length_pos hlen
    simpa using hsub e he
  · rintro r ⟨_, h⟩
    rw [reachIn_iff, gr, Finset.coe_empty, SimpleGraph.fromEdgeSet_empty,
      SimpleGraph.reachable_bot] at h
    exact h.symm

lemma exists_rootedSpanningForest {R : Finset (Fin n)} (hR : R.Nonempty) :
    ∃ F, IsRootedSpanningForest R F := by
  classical
  obtain ⟨r0, hr0⟩ := hR
  have key : ∀ S : Finset (Fin n), S ⊆ Rᶜ → ∃ F, IsRootedSpanningForest Sᶜ F := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _; exact ⟨∅, by simpa using isRootedSpanningForest_empty⟩
    | @insert v S hvS ih =>
      intro hsub
      obtain ⟨F, hF⟩ := ih (subset_trans (subset_insert _ _) hsub)
      have hvR : v ∉ R := by simpa using hsub (mem_insert_self v S)
      have hr0S : r0 ∈ Sᶜ := by
        rw [mem_compl]; intro h
        exact (mem_compl.mp (hsub (mem_insert_of_mem h))) hr0
      have hne : v ≠ r0 := fun h => hvR (h ▸ hr0)
      have := merge hF (v := v) (r0 := r0) (by simpa using hvS) hr0S hne
      rw [show Sᶜ.erase v = (insert v S)ᶜ by ext x; simp] at this
      exact ⟨_, this⟩
  simpa using key Rᶜ subset_rfl

/-- **Existence of a rooted MSF** for a nonempty root set. -/
theorem exists_rootedMSF (d : Fin n → Fin n → ℝ) {R : Finset (Fin n)} (hR : R.Nonempty) :
    ∃ F, IsRootedMSF d R F := by
  classical
  set S := (univ : Finset (Finset (Sym2 (Fin n)))).filter (fun F => IsRootedSpanningForest R F)
  obtain ⟨F0, hF0⟩ := exists_rootedSpanningForest hR
  obtain ⟨F, hF, hmin⟩ :=
    Finset.exists_min_image S (DoublingMST.treeWeight d) ⟨F0, by simp [S, hF0]⟩
  exact ⟨F, by simpa [S] using hF, fun F' hF' => hmin F' (by simp [S, hF'])⟩

/-! ### Cut property, path bound, candidate edges -/

section Main
variable {d : Fin n → Fin n → ℝ} {R : Finset (Fin n)} {F : Finset (Sym2 (Fin n))}

/-- **Cut property.** Removing `e ∈ F` from a rooted MSF leaves a rootless side; if `w` lies on
it (it reaches no root in `F \ {e}`) and `y` is outside `w`'s component of `F \ {e}`, then
`e` is no heavier than `d w y`. (No metric assumption needed.) -/
theorem cut_property (hF : IsRootedMSF d R F) {e : Sym2 (Fin n)} (he : e ∈ F) {w y : Fin n}
    (hw : ∀ r ∈ R, ¬ reachIn (F.erase e) w r) (hwy : ¬ reachIn (F.erase e) w y) :
    DoublingMST.edgeCost d e ≤ d w y := by
  classical
  induction e with
  | _ a b =>
  simp only [reachIn_iff] at hw hwy
  have hF' := exchange hF.1 he hw hwy
  have hle := hF.2 _ hF'
  have hnot : s(w, y) ∉ F.erase s(a, b) := fun h => hwy (SimpleGraph.Adj.reachable (by
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨h, fun h' => hwy (h' ▸ SimpleGraph.Reachable.refl _)⟩))
  unfold DoublingMST.treeWeight at hle
  rw [Finset.sum_insert hnot, ← Finset.add_sum_erase F _ he] at hle
  have : DoublingMST.edgeCost d s(w, y) ≤ d w y := min_le_left _ _
  linarith

/-- **Claim 9.5 path bound** (no metric assumption needed). -/
theorem path_bound' (hF : IsRootedMSF d R F) {v r : Fin n} (hr : r ∈ R) (hvr : reachIn F v r)
    {x : Fin n} (hx : x ∈ R) {e : Sym2 (Fin n)} (he : e ∈ MetricTSPSublinear.pathEdges F v r) :
    DoublingMST.edgeCost d e ≤ d v x := by
  unfold MetricTSPSublinear.pathEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨heF, hnr⟩ := he
  rw [← Finset.coe_erase] at hnr
  have hw : ∀ r' ∈ R, ¬ reachIn (F.erase e) v r' := by
    intro r' hr' h
    have := (hF.1.2 v).unique ⟨hr', reachIn_mono (Finset.erase_subset _ _) h⟩ ⟨hr, hvr⟩
    subst this
    exact hnr (reachIn_iff.mp h)
  exact cut_property hF heF hw (hw x hx)

/-- **Claim 9.5 path bound**: every edge on the path from `v` to its root `r` weighs at most
`d(v, x)` for every root `x`, i.e. at most `d(v, R)`. -/
theorem path_bound (_hd : DoublingMST.IsMetric d) (hF : IsRootedMSF d R F) {v r : Fin n}
    (hr : r ∈ R) (hvr : reachIn F v r) {x : Fin n} (hx : x ∈ R) {e : Sym2 (Fin n)}
    (he : e ∈ MetricTSPSublinear.pathEdges F v r) :
    DoublingMST.edgeCost d e ≤ d v x :=
  path_bound' hF hr hvr hx he

/-- **Claim 9.3 candidate edges**: every edge `(u, v)` of a rooted MSF for `R ⊇ S0` satisfies
`d(u,v) ≤ d(u,s)` for all `s ∈ S0`, or `d(u,v) ≤ d(v,s)` for all `s ∈ S0`. -/
theorem candidate (hd : DoublingMST.IsMetric d) (hF : IsRootedMSF d R F) {S0 : Finset (Fin n)}
    (hS0 : S0 ⊆ R) (_hne : S0.Nonempty) {u v : Fin n} (he : s(u, v) ∈ F) (_huv : u ≠ v) :
    (∀ s ∈ S0, d u v ≤ d u s) ∨ (∀ s ∈ S0, d u v ≤ d v s) := by
  have hc : DoublingMST.edgeCost d s(u, v) = d u v := by
    show min (d u v) (d v u) = d u v
    rw [hd.2.1 v u, min_self]
  rcases rootless_or hF.1 he with h | h
  · left
    intro s hs
    have := cut_property hF he (w := u) (y := s) (fun r hr hr' => h r hr (reachIn_iff.mp hr'))
      (fun hr' => h s (hS0 hs) (reachIn_iff.mp hr'))
    linarith
  · right
    intro s hs
    have := cut_property hF he (w := v) (y := s) (fun r hr hr' => h r hr (reachIn_iff.mp hr'))
      (fun hr' => h s (hS0 hs) (reachIn_iff.mp hr'))
    linarith

end Main

end MTSPRF

open MetricTSPSublinear in
theorem solution {n : ℕ} {d : Fin n → Fin n → ℝ} (hd : DoublingMST.IsMetric d)
    {R : Finset (Fin n)} {F : Finset (Sym2 (Fin n))} (hF : IsRootedMSF d R F) {S0 : Finset (Fin n)}
    (hS0 : S0 ⊆ R) {u v : Fin n} (he : s(u, v) ∈ F) :
    (∀ s ∈ S0, d u v ≤ d u s) ∨ (∀ s ∈ S0, d u v ≤ d v s) :=
  by
  by_cases hne : S0.Nonempty
  · by_cases huv : u = v
    · subst huv; left; intro s _
      have h1 := hd.2.2 u s u
      rw [(hd.1 u u).mpr rfl, hd.2.1 s u] at h1
      rw [(hd.1 u u).mpr rfl]; linarith
    · exact MTSPRF.candidate hd hF hS0 hne he huv
  · left; intro s hs; exact absurd ⟨s, hs⟩ hne
