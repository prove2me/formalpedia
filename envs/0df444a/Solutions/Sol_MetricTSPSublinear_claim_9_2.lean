-- Prove2me | solution 1 for MetricTSPSublinear.claim_9_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:09:13.564403+00:00
-- url     : https://prove2.me/submissions/74c46bd3-6920-4ffe-a147-766fb400c0cb

import Definitions.Def_MetricTSPSublinear_IsRootedMSF
import Definitions.Def_MetricTSPSublinear_rootedKruskal
import Definitions.Def_MetricTSPSublinear_treeDist
import Mathlib

/-!
# Rooted spanning forests: basic facts (copied from `Solutions/RF/RootedMSF.lean`, namespace `MTSPRF`)

Bridge between CombOpt walks and Mathlib simple graphs, the exchange lemma and existence of a rooted
MSF, restated for the published definitions `MetricTSPSublinear.{reachIn, IsRootedSpanningForest,
IsRootedMSF}`.
-/

namespace MTSPPK
open Finset CombOpt.SpanningTree MetricTSPSublinear MetricTSPSublinear.RootedKruskal

variable {n : ℕ}


/- The Mathlib simple graph of an edge set (loops dropped). -/
/- A Mathlib walk as a walk of the complete graph. -/
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

/- A walk of the complete graph whose edges are edges of `G`, as a Mathlib walk of `G`. -/
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

/- A forest contains no loop. -/
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

/- Deleting an edge `s(a, b)` of a forest disconnects `a` from `b`. -/
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

/- Reachability after adding one edge `s(a, b)`. -/
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

/- Removing an edge `s(a, b)` of a rooted spanning forest: one of `a`, `b` loses its root. -/
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

/- After removing `s(a, b)`, all rootless vertices lie in one component. -/
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

/- The exchange: reconnecting the rootless side by `s(w, y)` gives a rooted spanning forest. -/
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

/- Joining two distinct roots `r0`, `v` by an edge; `v` stops being a root. -/
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

/- **Existence of a rooted MSF** for a nonempty root set. -/
theorem exists_rootedMSF (d : Fin n → Fin n → ℝ) {R : Finset (Fin n)} (hR : R.Nonempty) :
    ∃ F, IsRootedMSF d R F := by
  classical
  set S := (univ : Finset (Finset (Sym2 (Fin n)))).filter (fun F => IsRootedSpanningForest R F)
  obtain ⟨F0, hF0⟩ := exists_rootedSpanningForest hR
  obtain ⟨F, hF, hmin⟩ :=
    Finset.exists_min_image S (DoublingMST.treeWeight d) ⟨F0, by simp [S, hF0]⟩
  exact ⟨F, by simpa [S] using hF, fun F' hF' => hmin F' (by simp [S, hF'])⟩

end MTSPPK


/-!
# The tie-broken rooted Kruskal forest

Azarmehr–Behnezhad, *Metric TSP in Sublinear Time*, arXiv:2611.04283, p.15: `F_root` is
"conceptually obtained using the Kruskal algorithm, except if the two endpoints of an edge are
already connected to roots in `S_root`, the edge is ignored"; ties are broken by edge IDs.

We fix the strict total order `key d e = (edgeCost d e, code e)` (lexicographic) on unordered pairs,
`code` an injection into `ℕ`. Processing pairs in increasing key order, Kruskal adds `e = s(a, b)`
iff `a`, `b` are in different components of the edges added so far and not both of these
components contain a root. Contracting `R` to one vertex (adding all root pairs `R.sym2`), this
means that `a` and `b` are disconnected in `gr (K_{<e} ∪ R.sym2)`, `K_{<e}` the edges of the
output processed before `e`. Since `K_{<e}` has the same connectivity (modulo roots) as *all*
pairs of key `< e` (`conn_below_inter`), the output is defined explicitly by
`kruskalRooted d R = {e off-diagonal | endpoints of e not connected in gr(below e ∪ R.sym2)}`,
and `mem_kruskalRooted_iff` / `kruskalRooted_unique` show it is exactly (and the unique set
satisfying) the Kruskal recursion.
-/

namespace MTSPPK
open Finset CombOpt.SpanningTree MetricTSPSublinear MetricTSPSublinear.RootedKruskal

variable {n : ℕ}

/-! ### The key order -/

/- A fixed injection of unordered pairs into `ℕ` (the edge IDs used for tie-breaking). -/
lemma code_injective : Function.Injective (code (n := n)) :=
  fun _ _ h => (Fintype.equivFin _).injective (Fin.ext h)

/- The tie-broken key: cost first, then edge ID. -/
lemma key_injective (d : Fin n → Fin n → ℝ) : Function.Injective (key d) := by
  intro a b h
  have := congrArg (fun p => (ofLex p).2) h
  exact code_injective this

lemma key_lt_of_le_of_ne {d : Fin n → Fin n → ℝ} {e f : Sym2 (Fin n)} (h : key d e ≤ key d f)
    (hne : e ≠ f) : key d e < key d f :=
  lt_of_le_of_ne h (fun h' => hne (key_injective d h'))

lemma edgeCost_le_of_key_lt {d : Fin n → Fin n → ℝ} {e f : Sym2 (Fin n)}
    (h : key d e < key d f) : DoublingMST.edgeCost d e ≤ DoublingMST.edgeCost d f := by
  unfold key at h
  rw [Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

/-! ### Connectivity modulo the roots -/

/- All pairs of key strictly smaller than `e`. -/
lemma mem_below {d : Fin n → Fin n → ℝ} {e f : Sym2 (Fin n)} :
    f ∈ below d e ↔ key d f < key d e := by
  unfold below; simp

/- `x`, `y` are connected in `S` once all roots are identified. -/
/- `x` is connected in `S` to some root. -/
lemma conn_symm {R : Finset (Fin n)} {S : Finset (Sym2 (Fin n))} {x y : Fin n}
    (h : conn R S x y) : conn R S y x := SimpleGraph.Reachable.symm h

lemma conn_mono {R : Finset (Fin n)} {S T : Finset (Sym2 (Fin n))} (hST : S ⊆ T) {x y : Fin n}
    (h : conn R S x y) : conn R T x y :=
  h.mono (gr_mono (Finset.union_subset_union hST subset_rfl))

lemma conn_of_mem {R : Finset (Fin n)} {S : Finset (Sym2 (Fin n))} {x y : Fin n}
    (h : s(x, y) ∈ S) : conn R S x y := by
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by
      rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨by simp [h], hxy⟩)

lemma conn_of_mem_R {R : Finset (Fin n)} {S : Finset (Sym2 (Fin n))} {x y : Fin n}
    (hx : x ∈ R) (hy : y ∈ R) : conn R S x y := by
  by_cases hxy : x = y
  · subst hxy; exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (by
      rw [SimpleGraph.fromEdgeSet_adj]
      refine ⟨?_, hxy⟩
      simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe, Finset.mem_sym2_iff]
      right; intro a ha
      rcases Sym2.mem_iff.mp ha with rfl | rfl <;> assumption)

/- Reachability modulo roots splits into plain reachability or both ends rooted. -/
lemma conn_split {R : Finset (Fin n)} {S : Finset (Sym2 (Fin n))} {x y : Fin n}
    (h : conn R S x y) : (gr S).Reachable x y ∨ (rooted R S x ∧ rooted R S y) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Or.inl (SimpleGraph.Reachable.refl _)
  | @cons x z y hxz p ih =>
    rw [SimpleGraph.fromEdgeSet_adj] at hxz
    obtain ⟨hmem, hne⟩ := hxz
    rw [Finset.coe_union, Set.mem_union] at hmem
    rcases hmem with hS | hR
    · have hr : (gr S).Reachable x z :=
        SimpleGraph.Adj.reachable (by rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨hS, hne⟩)
      rcases ih with h | ⟨⟨r, hr', h1⟩, h2⟩
      · exact Or.inl (hr.trans h)
      · exact Or.inr ⟨⟨r, hr', hr.trans h1⟩, h2⟩
    · rw [Finset.mem_coe, Finset.mem_sym2_iff] at hR
      have hx : x ∈ R := hR x (Sym2.mem_mk_left _ _)
      have hz : z ∈ R := hR z (Sym2.mem_mk_right _ _)
      refine Or.inr ⟨⟨x, hx, SimpleGraph.Reachable.refl _⟩, ?_⟩
      rcases ih with h | ⟨_, h2⟩
      · exact ⟨z, hz, h.symm⟩
      · exact h2

lemma conn_of_reach {R : Finset (Fin n)} {S : Finset (Sym2 (Fin n))} {x y : Fin n}
    (h : (gr S).Reachable x y) : conn R S x y :=
  h.mono (gr_mono Finset.subset_union_left)

lemma conn_of_rooted {R : Finset (Fin n)} {S : Finset (Sym2 (Fin n))} {x y : Fin n}
    (hx : rooted R S x) (hy : rooted R S y) : conn R S x y := by
  obtain ⟨r1, hr1, h1⟩ := hx
  obtain ⟨r2, hr2, h2⟩ := hy
  exact ((conn_of_reach h1).trans (conn_of_mem_R hr1 hr2)).trans (conn_of_reach h2.symm)

/- If every adjacency of `G` is a reachability of `H`, then so is every reachability. -/
lemma reach_of_adj_reach {G H : SimpleGraph (Fin n)} (hGH : ∀ u v, G.Adj u v → H.Reachable u v)
    {x y : Fin n} (h : G.Reachable x y) : H.Reachable x y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj _ ih => exact (hGH _ _ hadj).trans ih

/-! ### The rooted Kruskal forest -/

/- **The tie-broken rooted Kruskal forest.** An off-diagonal pair `e = s(a, b)` is taken iff `a`
and `b` are not connected, modulo the roots `R`, by pairs of smaller key. -/
section Kruskal
variable {d : Fin n → Fin n → ℝ} {R : Finset (Fin n)}

lemma mem_kruskalRooted {e : Sym2 (Fin n)} :
    e ∈ kruskalRooted d R ↔ ¬ e.IsDiag ∧ ∀ a b, e = s(a, b) → ¬ conn R (below d e) a b := by
  unfold kruskalRooted; simp

lemma not_conn_of_mem {a b : Fin n} (h : s(a, b) ∈ kruskalRooted d R) :
    a ≠ b ∧ ¬ conn R (below d s(a, b)) a b := by
  rw [mem_kruskalRooted] at h
  exact ⟨fun hab => h.1 (by simp [hab]), h.2 a b rfl⟩

lemma conn_of_not_mem {a b : Fin n} (hab : a ≠ b) (h : s(a, b) ∉ kruskalRooted d R) :
    conn R (below d s(a, b)) a b := by
  rw [mem_kruskalRooted] at h
  push Not at h
  obtain ⟨a', b', he, hc⟩ := h (by simpa using hab)
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hc
  · exact conn_symm hc

lemma below_ssubset {e f : Sym2 (Fin n)} (h : key d f < key d e) : below d f ⊂ below d e := by
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨f, mem_below.mpr h, fun h' => lt_irrefl _ (mem_below.mp h')⟩
  · intro g hg; exact mem_below.mpr ((mem_below.mp hg).trans h)

/- **Key lemma.** Modulo the roots, the Kruskal edges below `e` connect everything that the pairs
below `e` connect. -/
theorem conn_below_inter (e : Sym2 (Fin n)) {x y : Fin n} (h : conn R (below d e) x y) :
    conn R (kruskalRooted d R ∩ below d e) x y := by
  induction hc : (below d e).card using Nat.strong_induction_on generalizing e x y with
  | _ m ih =>
  subst hc
  refine reach_of_adj_reach (fun u v huv => ?_) h
  rw [SimpleGraph.fromEdgeSet_adj, Finset.coe_union, Set.mem_union] at huv
  obtain ⟨hmem, hne⟩ := huv
  rcases hmem with hb | hR
  · rw [Finset.mem_coe] at hb
    by_cases hK : s(u, v) ∈ kruskalRooted d R
    · exact conn_of_mem (Finset.mem_inter.mpr ⟨hK, hb⟩)
    · have hlt := mem_below.mp hb
      have h1 := ih _ (Finset.card_lt_card (below_ssubset hlt)) s(u, v) (conn_of_not_mem hne hK) rfl
      exact conn_mono (Finset.inter_subset_inter subset_rfl (below_ssubset hlt).subset) h1
  · rw [Finset.mem_coe, Finset.mem_sym2_iff] at hR
    exact conn_of_mem_R (hR u (Sym2.mem_mk_left _ _)) (hR v (Sym2.mem_mk_right _ _))

/- **Kruskal recursion.** `e` belongs to the output iff it is not a loop and its endpoints are
not connected, modulo the roots, by the output edges processed before `e` (i.e. they lie in
different components which do not both contain a root). -/
theorem mem_kruskalRooted_iff {e : Sym2 (Fin n)} :
    e ∈ kruskalRooted d R ↔
      ¬ e.IsDiag ∧ ∀ a b, e = s(a, b) → ¬ conn R (kruskalRooted d R ∩ below d e) a b := by
  rw [mem_kruskalRooted]
  refine and_congr_right fun _ => forall_congr' fun a => forall_congr' fun b =>
    imp_congr_right fun _ => not_congr ⟨conn_below_inter e, conn_mono Finset.inter_subset_right⟩

/- Same, in the explicit Kruskal form: different components, not both rooted. -/
theorem mem_kruskalRooted_iff' {a b : Fin n} :
    s(a, b) ∈ kruskalRooted d R ↔
      a ≠ b ∧ ¬ (gr (kruskalRooted d R ∩ below d s(a, b))).Reachable a b ∧
        ¬ (rooted R (kruskalRooted d R ∩ below d s(a, b)) a ∧
          rooted R (kruskalRooted d R ∩ below d s(a, b)) b) := by
  constructor
  · intro h
    have h' := (mem_kruskalRooted_iff.mp h).2 a b rfl
    exact ⟨(not_conn_of_mem h).1, fun h2 => h' (conn_of_reach h2),
      fun ⟨h2, h3⟩ => h' (conn_of_rooted h2 h3)⟩
  · rintro ⟨hab, h1, h2⟩
    refine mem_kruskalRooted_iff.mpr ⟨by simpa using hab, fun a' b' he hc => ?_⟩
    have hc' : conn R (kruskalRooted d R ∩ below d s(a, b)) a b := by
      rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hc
      · exact conn_symm hc
    rcases conn_split hc' with h | h
    · exact h1 h
    · exact h2 h

/- The Kruskal recursion determines the output uniquely. -/
theorem kruskalRooted_unique (K : Finset (Sym2 (Fin n)))
    (hK : ∀ e, e ∈ K ↔ ¬ e.IsDiag ∧ ∀ a b, e = s(a, b) → ¬ conn R (K ∩ below d e) a b) :
    K = kruskalRooted d R := by
  have key : ∀ e, (e ∈ K ↔ e ∈ kruskalRooted d R) := by
    intro e
    induction hc : (below d e).card using Nat.strong_induction_on generalizing e with
    | _ m ih =>
    subst hc
    have hint : K ∩ below d e = kruskalRooted d R ∩ below d e := by
      ext f
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨(ih _ (Finset.card_lt_card (below_ssubset (mem_below.mp h2))) f rfl).mp h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(ih _ (Finset.card_lt_card (below_ssubset (mem_below.mp h2))) f rfl).mpr h1, h2⟩
    rw [hK e, mem_kruskalRooted_iff, hint]
  ext e; exact key e

/-! ### It is a rooted spanning forest -/

/- Invariant: acyclic, and no two distinct roots are connected. -/
lemma invariant (S : Finset (Sym2 (Fin n))) (hS : S ⊆ kruskalRooted d R) :
    (gr S).IsAcyclic ∧ ∀ r1 ∈ R, ∀ r2 ∈ R, (gr S).Reachable r1 r2 → r1 = r2 := by
  classical
  induction S using Finset.induction_on_max_value (key d) with
  | empty =>
    refine ⟨?_, fun r1 _ r2 _ h => ?_⟩
    · simp only [gr, Finset.coe_empty, SimpleGraph.fromEdgeSet_empty]
      exact SimpleGraph.isAcyclic_bot
    · simp only [gr, Finset.coe_empty, SimpleGraph.fromEdgeSet_empty,
        SimpleGraph.reachable_bot] at h
      exact h
  | insert e S heS hmax ih =>
    obtain ⟨hac, hroot⟩ := ih (subset_trans (Finset.subset_insert _ _) hS)
    have heK := hS (Finset.mem_insert_self e S)
    induction e with
    | _ a b =>
    obtain ⟨hab, hnc⟩ := not_conn_of_mem heK
    have hSb : S ⊆ below d s(a, b) := fun x hx =>
      mem_below.mpr (key_lt_of_le_of_ne (hmax x hx) (fun h => heS (h ▸ hx)))
    have hnc' : ¬ conn R S a b := fun h => hnc (conn_mono hSb h)
    have hnr : ¬ (gr S).Reachable a b := fun h => hnc' (conn_of_reach h)
    have hsub : ∀ f ∈ insert s(a, b) S, f ∈ S ∨ f = s(a, b) := by
      intro f hf
      rcases Finset.mem_insert.mp hf with h | h
      · exact Or.inr h
      · exact Or.inl h
    refine ⟨?_, fun r1 hr1 r2 hr2 h => ?_⟩
    · rw [gr_insert]; exact hac.sup_edge_of_not_reachable hnr
    · rcases reach_split hsub h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hroot r1 hr1 r2 hr2 h
      · exact absurd (conn_of_rooted ⟨r1, hr1, h1.symm⟩ ⟨r2, hr2, h2⟩) hnc'
      · exact absurd (conn_of_rooted ⟨r2, hr2, h2⟩ ⟨r1, hr1, h1.symm⟩) hnc'

theorem kruskal_isRootedSpanningForest (hR : R.Nonempty) :
    IsRootedSpanningForest R (kruskalRooted d R) := by
  obtain ⟨hac, hroot⟩ := invariant (d := d) (R := R) _ subset_rfl
  refine ⟨isForest_of_isAcyclic (fun e he => (mem_kruskalRooted.mp he).1) hac, fun v => ?_⟩
  obtain ⟨r0, hr0⟩ := hR
  have hex : rooted R (kruskalRooted d R) v := by
    by_cases hv : v = r0
    · exact ⟨r0, hr0, hv ▸ SimpleGraph.Reachable.refl _⟩
    · by_cases hK : s(v, r0) ∈ kruskalRooted d R
      · exact ⟨r0, hr0, SimpleGraph.Adj.reachable (by
          rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨hK, hv⟩)⟩
      · have h := conn_mono Finset.inter_subset_left
          (conn_below_inter _ (conn_of_not_mem hv hK))
        rcases conn_split h with h | ⟨h, _⟩
        · exact ⟨r0, hr0, h⟩
        · exact h
  obtain ⟨r, hr, hvr⟩ := hex
  refine ⟨r, ⟨hr, reachIn_iff.mpr hvr⟩, fun r' ⟨hr', h'⟩ => ?_⟩
  exact hroot r' hr' r hr ((reachIn_iff.mp h').symm.trans hvr)

/-! ### Strict cut property -/

/- **Strict cut property.** Remove `e` from the rooted Kruskal forest; `w` lies on the rootless
side (it reaches no root in `K \ {e}`) and `y` outside it (it reaches a root in `K \ {e}`). Then
every pair `s(w, y) ≠ e` across this cut has strictly larger key than `e`. -/
theorem kruskal_cut_strict {e : Sym2 (Fin n)} (_he : e ∈ kruskalRooted d R) {w y : Fin n}
    (hw : ∀ r ∈ R, ¬ reachIn ((kruskalRooted d R).erase e) w r)
    (hy : ∃ r ∈ R, reachIn ((kruskalRooted d R).erase e) y r) (hne : s(w, y) ≠ e) :
    key d e < key d s(w, y) := by
  obtain ⟨ry, hry, hyr⟩ := hy
  rw [reachIn_iff] at hyr
  have hw' : ∀ r ∈ R, ¬ (gr ((kruskalRooted d R).erase e)).Reachable w r :=
    fun r hr h => hw r hr (reachIn_iff.mpr h)
  rcases lt_trichotomy (key d e) (key d s(w, y)) with h | h | h
  · exact h
  · exact absurd (key_injective d h).symm hne
  · exfalso
    have hc : conn R (below d e) w y := conn_of_mem (mem_below.mpr h)
    have hsub : kruskalRooted d R ∩ below d e ⊆ (kruskalRooted d R).erase e := by
      intro f hf
      rw [Finset.mem_inter, mem_below] at hf
      exact Finset.mem_erase.mpr ⟨fun h' => lt_irrefl _ (h' ▸ hf.2), hf.1⟩
    rcases conn_split (conn_mono hsub (conn_below_inter e hc)) with h1 | ⟨⟨r, hr, h1⟩, _⟩
    · exact hw' ry hry (h1.trans hyr)
    · exact hw' r hr h1

/-! ### Minimality -/

lemma eq_of_subset {F1 F2 : Finset (Sym2 (Fin n))} (h1 : IsRootedSpanningForest R F1)
    (h2 : IsRootedSpanningForest R F2) (hsub : F1 ⊆ F2) : F1 = F2 := by
  refine Finset.Subset.antisymm hsub fun e he => ?_
  by_contra heF
  induction e with
  | _ a b =>
  have hs : F1 ⊆ F2.erase s(a, b) := fun f hf =>
    Finset.mem_erase.mpr ⟨fun h => heF (h ▸ hf), hsub hf⟩
  rcases rootless_or h2 he with h | h
  · obtain ⟨r, hr, har⟩ := exists_root h1 a
    exact h r hr (har.mono (gr_mono hs))
  · obtain ⟨r, hr, hbr⟩ := exists_root h1 b
    exact h r hr (hbr.mono (gr_mono hs))

/- One exchange step: an MSF edge `s(a, b)` outside the Kruskal forest, `a` on the rootless side,
can be swapped for a Kruskal edge. -/
lemma exchange_step {M : Finset (Sym2 (Fin n))} (hM : IsRootedMSF d R M) {a b : Fin n}
    (hf : s(a, b) ∈ M) (hfK : s(a, b) ∉ kruskalRooted d R)
    (ha : ∀ r ∈ R, ¬ (gr (M.erase s(a, b))).Reachable a r) :
    ∃ M', IsRootedMSF d R M' ∧ (M' \ kruskalRooted d R).card < (M \ kruskalRooted d R).card := by
  classical
  set K := kruskalRooted d R
  set f := s(a, b) with hfdef
  have hab : a ≠ b := fun h => not_isDiag_of_isForest hM.1.1 hf (by simp [f, h])
  have hb : ∃ r ∈ R, (gr (M.erase f)).Reachable b r := by
    by_contra hb
    push Not at hb
    exact not_reach_erase hM.1.1 hf (rootless_conn hM.1 hf ha hb)
  obtain ⟨p⟩ := conn_below_inter (d := d) (R := R) f (conn_of_not_mem hab hfK)
  obtain ⟨dt, -, hfst, hsnd⟩ := p.exists_boundary_dart
    {x | ∀ r ∈ R, ¬ (gr (M.erase f)).Reachable x r} ha (by simpa using hb)
  set w := dt.fst
  set y := dt.snd
  have hadj := dt.adj
  rw [SimpleGraph.fromEdgeSet_adj, Finset.coe_union, Set.mem_union] at hadj
  obtain ⟨hmem, hwy⟩ := hadj
  have hw : ∀ r ∈ R, ¬ (gr (M.erase f)).Reachable w r := hfst
  have hgK : s(w, y) ∈ K ∩ below d f := by
    rcases hmem with h | h
    · exact h
    · rw [Finset.mem_coe, Finset.mem_sym2_iff] at h
      exact absurd (SimpleGraph.Reachable.refl _) (hw w (h w (Sym2.mem_mk_left _ _)))
  rw [Finset.mem_inter, mem_below] at hgK
  have hy : ∃ r ∈ R, (gr (M.erase f)).Reachable y r := by simpa using hsnd
  obtain ⟨ry, hry, hyr⟩ := hy
  have hnr : ¬ (gr (M.erase f)).Reachable w y := fun h => hw ry hry (h.trans hyr)
  have hF' := exchange hM.1 hf hw hnr
  have hnot : s(w, y) ∉ M.erase f := fun h => hnr (SimpleGraph.Adj.reachable (by
    rw [SimpleGraph.fromEdgeSet_adj]; exact ⟨h, hwy⟩))
  have hcost := edgeCost_le_of_key_lt hgK.2
  have hwt : DoublingMST.treeWeight d (insert s(w, y) (M.erase f)) ≤
      DoublingMST.treeWeight d M := by
    unfold DoublingMST.treeWeight
    rw [Finset.sum_insert hnot, ← Finset.add_sum_erase M _ hf]
    linarith
  refine ⟨insert s(w, y) (M.erase f), ⟨hF', fun F' hF'' => hwt.trans (hM.2 F' hF'')⟩, ?_⟩
  have hsub : insert s(w, y) (M.erase f) \ K ⊆ (M \ K).erase f := by
    intro g hg
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase] at hg ⊢
    rcases hg with ⟨h | ⟨h1, h2⟩, h3⟩
    · exact absurd (h ▸ hgK.1) h3
    · exact ⟨h1, h2, h3⟩
  exact lt_of_le_of_lt (Finset.card_le_card hsub)
    (Finset.card_erase_lt_of_mem (Finset.mem_sdiff.mpr ⟨hf, hfK⟩))

/- **(a)** The tie-broken rooted Kruskal forest is a rooted minimum spanning forest. -/
theorem kruskal_isRootedMSF (hR : R.Nonempty) : IsRootedMSF d R (kruskalRooted d R) := by
  classical
  have hK := kruskal_isRootedSpanningForest (d := d) hR
  suffices h : ∀ m, ∀ M, IsRootedMSF d R M → (M \ kruskalRooted d R).card = m →
      ∃ M', IsRootedMSF d R M' ∧ M' ⊆ kruskalRooted d R by
    obtain ⟨M0, hM0⟩ := exists_rootedMSF d hR
    obtain ⟨M, hM, hsub⟩ := h _ M0 hM0 rfl
    rw [← eq_of_subset hM.1 hK hsub]; exact hM
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro M hM hm
  by_cases hsub : M ⊆ kruskalRooted d R
  · exact ⟨M, hM, hsub⟩
  obtain ⟨f, hfM, hfK⟩ := Finset.not_subset.mp hsub
  induction f with
  | _ a b =>
  rcases rootless_or hM.1 hfM with h | h
  · obtain ⟨M', hM', hlt⟩ := exchange_step hM hfM hfK h
    exact ih _ (hm ▸ hlt) M' hM' rfl
  · rw [Sym2.eq_swap] at hfM hfK h
    obtain ⟨M', hM', hlt⟩ := exchange_step hM hfM hfK h
    exact ih _ (hm ▸ hlt) M' hM' rfl

end Kruskal

end MTSPPK


/-!
# Prim from a vertex finds the root path (Claim 9.2)

Azarmehr–Behnezhad, *Metric TSP in Sublinear Time*, arXiv:2611.04283, Claim 9.2: "we run Prim's
algorithm starting with `{v}` and continue until a vertex of `S_root` is reached". Starting from
`X = {v}`, while `X ∩ R = ∅`, add the minimum-key pair `(x, y)`, `x ∈ X`, `y ∉ X` (at most `n`
rounds). Every chosen edge lies in the rooted Kruskal forest, the process stops exactly when it
reaches a vertex of `R`, and that vertex is the root of `v`'s component; the chosen edges contain
the whole forest path from `v` to its root.
-/

namespace MTSPPK
open Finset CombOpt.SpanningTree MetricTSPSublinear MetricTSPSublinear.RootedKruskal

variable {n : ℕ}

/- The vertices reached: `v` followed by the new endpoints of the chosen pairs. -/
/- The edges of the chosen pairs. -/
/- The minimum-key pair `(x, y)` with `x ∈ X`, `y ∉ X`, if there is one. -/
/- The pairs chosen in the first `k` rounds of Prim from `v`, stopping once a root is reached. -/
/- **Prim's path from `v`** (`n` rounds suffice): the edges added. -/
/- The vertices in the order they are added (starting with `v`). -/
/- The last vertex added: the root found. -/
section Prim
variable {d : Fin n → Fin n → ℝ} {R : Finset (Fin n)}

lemma primStep_spec {X : Finset (Fin n)} {p : Fin n × Fin n} (h : primStep d X = some p) :
    p.1 ∈ X ∧ p.2 ∉ X ∧ ∀ q ∈ X ×ˢ Xᶜ, key d s(p.1, p.2) ≤ key d s(q.1, q.2) := by
  unfold primStep at h
  split_ifs at h with hne
  obtain rfl := Option.some.inj h
  have hs := Classical.choose_spec
    (Finset.exists_min_image (X ×ˢ Xᶜ) (fun p => key d s(p.1, p.2)) hne)
  obtain ⟨hmem, hmin⟩ := hs
  rw [Finset.mem_product, Finset.mem_compl] at hmem
  exact ⟨hmem.1, hmem.2, hmin⟩

lemma primStep_ne_none {X : Finset (Fin n)} (h : (X ×ˢ Xᶜ).Nonempty) : primStep d X ≠ none := by
  unfold primStep; simp [h]

/- **Prim's edge is a Kruskal edge**: when `X` contains no root, the minimum-key pair leaving `X`
belongs to the rooted Kruskal forest. -/
theorem prim_edge_mem {X : Finset (Fin n)} (hdis : Disjoint X R) {x y : Fin n} (hx : x ∈ X)
    (hy : y ∉ X) (hmin : ∀ q ∈ X ×ˢ Xᶜ, key d s(x, y) ≤ key d s(q.1, q.2)) :
    s(x, y) ∈ kruskalRooted d R := by
  have hxy : x ≠ y := fun h => hy (h ▸ hx)
  by_contra hK
  obtain ⟨p⟩ := conn_of_not_mem (d := d) (R := R) hxy hK
  obtain ⟨dt, -, h1, h2⟩ := p.exists_boundary_dart (X : Set (Fin n)) hx hy
  have hadj := dt.adj
  rw [SimpleGraph.fromEdgeSet_adj, Finset.coe_union, Set.mem_union] at hadj
  rcases hadj.1 with h | h
  · rw [Finset.mem_coe, mem_below] at h
    have := hmin (dt.fst, dt.snd) (Finset.mem_product.mpr ⟨h1, Finset.mem_compl.mpr h2⟩)
    exact lt_irrefl _ (lt_of_lt_of_le h this)
  · rw [Finset.mem_coe, Finset.mem_sym2_iff] at h
    exact Finset.disjoint_left.mp hdis h1 (h _ (Sym2.mem_mk_left _ _))

lemma mem_vset {v x : Fin n} {L : List (Fin n × Fin n)} :
    x ∈ vset v L ↔ x ∈ v :: L.map Prod.snd := by
  unfold vset; simp

lemma vset_append (v : Fin n) (L : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    vset v (L ++ [p]) = insert p.2 (vset v L) := by
  ext x; simp only [mem_vset, Finset.mem_insert]; simp; tauto

lemma pedges_append (L : List (Fin n × Fin n)) (p : Fin n × Fin n) :
    pedges (L ++ [p]) = insert s(p.1, p.2) (pedges L) := by
  ext x; unfold pedges; simp

/- The invariants of Prim's rounds. -/
structure Inv (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) (v : Fin n) (k : ℕ)
    (L : List (Fin n × Fin n)) : Prop where
  edges : ∀ p ∈ L, s(p.1, p.2) ∈ kruskalRooted d R
  fst : ∀ p ∈ L, p.1 ∈ vset v L
  reach : ∀ x ∈ vset v L, (gr (pedges L)).Reachable v x
  noroot : ∀ x ∈ (v :: L.map Prod.snd).dropLast, x ∉ R
  nodup : (v :: L.map Prod.snd).Nodup
  card : R.Nonempty → Disjoint (vset v L) R → k + 1 ≤ (vset v L).card

lemma inv_primPairs (v : Fin n) (k : ℕ) : Inv d R v k (primPairs d R v k) := by
  induction k with
  | zero =>
    show Inv d R v 0 []
    refine ⟨by simp, by simp, fun x hx => ?_, by simp, by simp, fun _ _ => ?_⟩
    · rw [mem_vset] at hx
      simp only [List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]
    · simp [vset]
  | succ k ih =>
    set L := primPairs d R v k with hL
    have hunf : primPairs d R v (k + 1) = if Disjoint (vset v L) R then
        (match primStep d (vset v L) with
          | none => L
          | some p => L ++ [p]) else L := rfl
    by_cases hdis : Disjoint (vset v L) R
    · rw [if_pos hdis] at hunf
      cases hp : primStep d (vset v L) with
      | none =>
        rw [hp] at hunf
        rw [hunf]
        refine ⟨ih.edges, ih.fst, ih.reach, ih.noroot, ih.nodup, fun hR _ => ?_⟩
        exfalso
        obtain ⟨r, hr⟩ := hR
        refine primStep_ne_none (d := d) ⟨(v, r), ?_⟩ hp
        rw [Finset.mem_product, Finset.mem_compl]
        exact ⟨mem_vset.mpr (List.mem_cons_self), fun h => Finset.disjoint_left.mp hdis h hr⟩
      | some p =>
        rw [hp] at hunf
        dsimp only at hunf
        rw [hunf]
        obtain ⟨h1, h2, hmin⟩ := primStep_spec hp
        have hne : p.1 ≠ p.2 := fun h => h2 (h ▸ h1)
        refine ⟨fun q hq => ?_, fun q hq => ?_, fun x hx => ?_, fun x hx => ?_, ?_, fun _ _ => ?_⟩
        · rcases List.mem_append.mp hq with hq | hq
          · exact ih.edges q hq
          · rw [List.mem_singleton] at hq
            subst hq
            exact prim_edge_mem hdis h1 h2 hmin
        · rw [vset_append]
          rcases List.mem_append.mp hq with hq | hq
          · exact Finset.mem_insert_of_mem (ih.fst q hq)
          · rw [List.mem_singleton] at hq
            subst hq
            exact Finset.mem_insert_of_mem h1
        · rw [vset_append, Finset.mem_insert] at hx
          rw [pedges_append, gr_insert]
          rcases hx with rfl | hx
          · refine ((ih.reach _ h1).mono le_sup_left).trans ?_
            exact SimpleGraph.Adj.reachable (Or.inr (by simp [SimpleGraph.edge_adj, hne]))
          · exact (ih.reach x hx).mono le_sup_left
        · have : (v :: (L ++ [p]).map Prod.snd).dropLast = v :: L.map Prod.snd := by
            rw [List.map_append, List.map_singleton, ← List.cons_append, List.dropLast_concat]
          rw [this] at hx
          exact fun hxR => Finset.disjoint_left.mp hdis (mem_vset.mpr hx) hxR
        · have : v :: (L ++ [p]).map Prod.snd = (v :: L.map Prod.snd) ++ [p.2] := by simp
          rw [this, List.nodup_append]
          refine ⟨ih.nodup, List.nodup_singleton _, fun a ha b hb => ?_⟩
          rw [List.mem_singleton] at hb
          subst hb
          rintro rfl
          exact h2 (mem_vset.mpr ha)
        · rw [vset_append, Finset.card_insert_of_notMem h2]
          have := ih.card ‹_› hdis
          omega
    · rw [if_neg hdis] at hunf
      rw [hunf]
      exact ⟨ih.edges, ih.fst, ih.reach, ih.noroot, ih.nodup, fun _ h => absurd h hdis⟩

/-! ### Main statements -/

/- Every edge added by Prim from `v` belongs to the rooted Kruskal forest. -/
theorem primPath_mem_kruskal (v : Fin n) {e : Sym2 (Fin n)} (he : e ∈ primPath d R v) :
    e ∈ kruskalRooted d R := by
  unfold primPath at he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  exact (inv_primPairs v n).edges p hp

/- If `v` is itself a root, Prim adds nothing. -/
theorem primPath_eq_nil {v : Fin n} (hv : v ∈ R) : primPath d R v = [] := by
  have : ∀ k, primPairs d R v k = [] := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      have hnd : ¬ Disjoint (vset v (primPairs d R v k)) R := fun h =>
        Finset.disjoint_left.mp h (mem_vset.mpr (List.mem_cons_self)) hv
      show (if Disjoint (vset v (primPairs d R v k)) R then _ else _) = []
      rw [if_neg hnd, ih]
  simp [primPath, this]

/- The vertices are added without repetition. -/
theorem primVerts_nodup (v : Fin n) : (primVerts d R v).Nodup := (inv_primPairs v n).nodup

/- No vertex before the last one is a root: the process continues while no root is reached. -/
theorem primVerts_dropLast_not_mem (v : Fin n) {x : Fin n} (hx : x ∈ (primVerts d R v).dropLast) :
    x ∉ R := (inv_primPairs v n).noroot x hx

/- Within `n` rounds a root is reached: the last vertex added is a root. -/
theorem primRoot_mem (hR : R.Nonempty) (v : Fin n) : primRoot d R v ∈ R := by
  have hI := inv_primPairs (d := d) (R := R) v n
  have hnd : ¬ Disjoint (vset v (primPairs d R v n)) R := by
    intro h
    have h1 := hI.card hR h
    have h2 := Finset.card_le_univ (vset v (primPairs d R v n))
    rw [Fintype.card_fin] at h2
    omega
  rw [Finset.not_disjoint_iff] at hnd
  obtain ⟨x, hx, hxR⟩ := hnd
  rw [mem_vset] at hx
  have hsplit := List.dropLast_append_getLast (List.cons_ne_nil v ((primPairs d R v n).map Prod.snd))
  rw [← hsplit, List.mem_append] at hx
  rcases hx with hx | hx
  · exact absurd hxR (hI.noroot x hx)
  · rw [List.mem_singleton] at hx
    rw [hx] at hxR
    exact hxR

lemma primRoot_mem_vset (v : Fin n) : primRoot d R v ∈ vset v (primPairs d R v n) :=
  mem_vset.mpr (List.getLast_mem _)

lemma pedges_subset (v : Fin n) : pedges (primPairs d R v n) ⊆ kruskalRooted d R := by
  intro e he
  unfold pedges at he
  rw [List.mem_toFinset] at he
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp he
  exact (inv_primPairs v n).edges p hp

/- The root found is reachable from `v` in the rooted Kruskal forest. -/
theorem reachIn_primRoot (v : Fin n) : reachIn (kruskalRooted d R) v (primRoot d R v) :=
  reachIn_iff.mpr (((inv_primPairs v n).reach _ (primRoot_mem_vset v)).mono
    (gr_mono (pedges_subset v)))

/- **Claim 9.2.** The vertex of `R` reached by Prim from `v` is the root of `v`'s component in the
rooted Kruskal forest. -/
theorem primRoot_eq_root (hR : R.Nonempty) (v : Fin n) {r : Fin n} (hr : r ∈ R) :
    reachIn (kruskalRooted d R) v r ↔ r = primRoot d R v := by
  constructor
  · intro h
    exact ((kruskal_isRootedSpanningForest (d := d) hR).2 v).unique ⟨hr, h⟩
      ⟨primRoot_mem hR v, reachIn_primRoot v⟩
  · rintro rfl; exact reachIn_primRoot v

/- The edges added by Prim contain the whole forest path from `v` to its root. -/
theorem pathEdges_subset_primPath (v : Fin n) :
    pathEdges (kruskalRooted d R) v (primRoot d R v) ⊆ (primPath d R v).toFinset := by
  intro e he
  unfold pathEdges at he
  rw [Finset.mem_filter] at he
  obtain ⟨_, hnr⟩ := he
  by_contra heP
  apply hnr
  refine ((inv_primPairs v n).reach _ (primRoot_mem_vset v)).mono
    (SimpleGraph.fromEdgeSet_mono ?_)
  intro f hf
  refine ⟨pedges_subset v hf, ?_⟩
  rintro rfl
  exact heP (by simpa [pedges, primPath] using hf)

/- The vertices of that path are all among Prim's vertices (`X` at the end). -/
theorem pathEdges_verts_subset (v : Fin n) {e : Sym2 (Fin n)}
    (he : e ∈ pathEdges (kruskalRooted d R) v (primRoot d R v)) {x : Fin n} (hx : x ∈ e) :
    x ∈ primVerts d R v := by
  have h := pathEdges_subset_primPath v he
  rw [List.mem_toFinset] at h
  unfold primPath at h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
  rcases Sym2.mem_iff.mp hx with rfl | rfl
  · exact mem_vset.mp ((inv_primPairs v n).fst p hp)
  · exact List.mem_cons_of_mem _ (List.mem_map_of_mem hp)

end Prim

end MTSPPK

open MetricTSPSublinear in
theorem solution {n : ℕ} (d : Fin n → Fin n → ℝ) (R : Finset (Fin n)) (hR : R.Nonempty) (v : Fin n) :
    IsRootedMSF d R (RootedKruskal.kruskalRooted d R) ∧
    RootedKruskal.primRoot d R v ∈ R ∧
    reachIn (RootedKruskal.kruskalRooted d R) v (RootedKruskal.primRoot d R v) ∧
    (∀ e ∈ RootedKruskal.primPath d R v, e ∈ RootedKruskal.kruskalRooted d R) ∧
    pathEdges (RootedKruskal.kruskalRooted d R) v (RootedKruskal.primRoot d R v) ⊆
      (RootedKruskal.primPath d R v).toFinset :=
  ⟨MTSPPK.kruskal_isRootedMSF hR, MTSPPK.primRoot_mem hR v, MTSPPK.reachIn_primRoot v,
    fun e he => MTSPPK.primPath_mem_kruskal v he, MTSPPK.pathEdges_subset_primPath v⟩
