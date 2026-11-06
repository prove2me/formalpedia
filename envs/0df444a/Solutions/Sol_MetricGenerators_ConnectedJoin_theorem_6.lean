-- Prove2me | solution 1 for MetricGenerators.ConnectedJoin.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:10:30.684532+00:00
-- url     : https://prove2.me/submissions/0acd26b2-773e-4033-b47f-9e38dc5b7a98

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TJoin
import Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric
import Theorems.Thm_MetricGenerators_ConnectedJoin_minimal_realization_unique
import Theorems.Thm_MetricGenerators_ConnectedJoin_lemma_2
import Theorems.Thm_MetricGenerators_ConnectedJoin_image_of_realization

open SimpleGraph MetricGenerators.FewComponents MetricGenerators.ConnectedJoin

namespace CJThm6Aux

theorem leaf_min {N : ℕ} (A : SimpleGraph (Fin N)) [DecidableRel A.Adj] (hA : A.IsTree)
    (S : Set (Fin N)) (hS : ∀ a, A.degree a = 1 → a ∈ S)
    (A' : A.Subgraph) (hc : A'.Connected) (hsub : S ⊆ A'.verts) : A'.verts = Set.univ := by
  classical
  by_contra hne
  obtain ⟨r, hr⟩ := hc.nonempty
  have hW : (Finset.univ.filter (fun v => v ∉ A'.verts)).Nonempty := by
    obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).1 hne
    exact ⟨v, by simp [hv]⟩
  obtain ⟨v, hvW, hvmax⟩ := Finset.exists_max_image _ (fun v => A.dist r v) hW
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hvW hvmax
  have hrv : r ≠ v := fun h => hvW (h ▸ hr)
  obtain ⟨p, hp, hplen⟩ := hA.connected.exists_path_of_dist r v
  have hpnil : ¬ p.reverse.Nil := by
    rw [← Walk.length_eq_zero_iff]; simp only [Walk.length_reverse]
    intro h0
    exact hrv (Walk.eq_of_length_eq_zero h0)
  set w := p.reverse.snd with hw
  have hvw : A.Adj v w := Walk.adj_snd hpnil
  have hdeg : A.degree v ≠ 1 := fun h1 => hvW (hsub (hS v h1))
  have hdeg0 : 0 < A.degree v := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.2 ⟨w, by simpa using hvw⟩
  obtain ⟨u, hu, huw⟩ : ∃ u ∈ A.neighborFinset v, u ≠ w := by
    by_contra hcon
    push Not at hcon
    have : A.neighborFinset v ⊆ {w} := fun x hx => by simpa using hcon x hx
    have := Finset.card_le_card this
    rw [card_neighborFinset_eq_degree] at this
    simp at this; omega
  rw [mem_neighborFinset] at hu
  obtain ⟨q, hq, hvq⟩ : ∃ q : A.Walk r u, q.IsPath ∧ v ∉ q.support := by
    by_cases huA : u ∈ A'.verts
    · obtain ⟨q0⟩ := hc.preconnected ⟨r, hr⟩ ⟨u, huA⟩
      let q1 : A.Walk r u := q0.map A'.hom
      have hsupp : ∀ x ∈ q1.support, x ∈ A'.verts := by
        intro x hx
        have hx' : x ∈ (q0.map A'.hom).support := hx
        rw [Walk.support_map, List.mem_map] at hx'
        obtain ⟨y, _, rfl⟩ := hx'
        exact y.2
      refine ⟨q1.bypass, q1.bypass_isPath, fun hv => hvW ?_⟩
      exact hsupp v (q1.support_bypass_subset_support hv)
    · have hle : A.dist r u ≤ A.dist r v := hvmax u huA
      obtain ⟨q, hq, hqlen⟩ := hA.connected.exists_path_of_dist r u
      refine ⟨q, hq, fun hv => ?_⟩
      have h1 := q.length_takeUntil_lt_length hv hu.ne
      have h2 := dist_le (q.takeUntil v hv)
      omega
  have hp1 : (Walk.cons hu q.reverse).IsPath :=
    hq.reverse.cons (by simpa using hvq)
  have heq := (hA.isAcyclic.subsingleton_path _ _).elim ⟨_, hp1⟩ ⟨p.reverse, hp.reverse⟩
  have : (Walk.cons hu q.reverse).snd = p.reverse.snd := by
    rw [Subtype.mk.injEq] at heq; rw [heq]
  rw [Walk.snd_cons] at this
  exact huw (this.trans hw.symm)

theorem hom_dist_le {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β} (f : A →g B)
    {a b : α} (h : A.Reachable a b) : B.dist (f a) (f b) ≤ A.dist a b := by
  obtain ⟨p, hp⟩ := h.exists_walk_length_eq_dist
  calc B.dist (f a) (f b) ≤ (p.map f).length := dist_le _
    _ = A.dist a b := by rw [Walk.length_map, hp]

theorem iso_dist {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B)
    (hA : A.Connected) (a b : α) : B.dist (ψ a) (ψ b) = A.dist a b := by
  apply le_antisymm (hom_dist_le ψ.toHom (hA a b))
  have hr : B.Reachable (ψ a) (ψ b) := (hA a b).map ψ.toHom
  have := hom_dist_le ψ.symm.toHom hr
  simpa using this

theorem iso_degree {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β} (ψ : A ≃g B) (a : α)
    [Fintype (A.neighborSet a)] [Fintype (B.neighborSet (ψ a))] :
    B.degree (ψ a) = A.degree a := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  exact (Fintype.card_congr (ψ.toEquiv.subtypeEquiv (fun x => by
    simp only [mem_neighborSet]; exact ψ.map_adj_iff.symm))).symm

theorem support_mem {V : Type*} (F : Finset (Sym2 V)) {a b : V}
    (w : (edgeGraph F).Walk a b) (ha : a ∈ edgeSupport F) :
    ∀ z ∈ w.support, z ∈ edgeSupport F := by
  induction w with
  | nil => intro z hz; simp at hz; exact hz ▸ ha
  | @cons x y c h p ih =>
    have hy : y ∈ edgeSupport F := by
      simp only [edgeGraph, fromEdgeSet_adj] at h
      exact ⟨s(x, y), h.1, by simp⟩
    intro z hz
    rw [Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact ha
    · exact ih hy z hz

theorem induce_dist {V : Type*} (F : Finset (Sym2 V))
    (hconn : ((edgeGraph F).induce (edgeSupport F)).Connected)
    (x y : ↥(edgeSupport F)) :
    ((edgeGraph F).induce (edgeSupport F)).dist x y = (edgeGraph F).dist x.1 y.1 := by
  apply le_antisymm _ (hom_dist_le (Embedding.induce (edgeSupport F)).toHom (hconn x y))
  have hr : (edgeGraph F).Reachable x.1 y.1 :=
    (hconn x y).map (Embedding.induce (edgeSupport F)).toHom
  obtain ⟨w, hw⟩ := hr.exists_walk_length_eq_dist
  have hs := support_mem F w x.2
  have := dist_le (w.induce (edgeSupport F) hs)
  have hl : (w.induce (edgeSupport F) hs).length = w.length := by
    have := congrArg Walk.length (Walk.map_induce w hs)
    rw [Walk.length_map] at this
    exact this
  rw [hl, hw] at this
  exact this

theorem degree_eq {V : Type*} [DecidableEq V] (G : SimpleGraph V) (F : Finset (Sym2 V))
    (hFG : (↑F : Set (Sym2 V)) ⊆ G.edgeSet) (v : ↥(edgeSupport F))
    [Fintype (((edgeGraph F).induce (edgeSupport F)).neighborSet v)] :
    ((edgeGraph F).induce (edgeSupport F)).degree v = edgeDeg F v.1 := by
  classical
  rw [← card_neighborFinset_eq_degree, edgeDeg]
  refine Finset.card_bij (fun w _ => s(v.1, w.1)) ?_ ?_ ?_
  · intro w hw
    rw [mem_neighborFinset, induce_adj] at hw
    simp only [edgeGraph, fromEdgeSet_adj] at hw
    exact Finset.mem_filter.2 ⟨Finset.mem_coe.1 hw.1, by simp⟩
  · intro a _ b _ hab
    exact Subtype.ext (Sym2.congr_right.1 hab)
  · intro e he
    rw [Finset.mem_filter] at he
    obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.1 he.2
    have hne : v.1 ≠ w := by
      intro h
      apply G.not_isDiag_of_mem_edgeSet (hFG he.1)
      simp [h]
    have hwS : w ∈ edgeSupport F := ⟨s(v.1, w), he.1, by simp⟩
    refine ⟨⟨w, hwS⟩, ?_, rfl⟩
    rw [mem_neighborFinset, induce_adj]
    simp only [edgeGraph, fromEdgeSet_adj]
    exact ⟨he.1, hne⟩

end CJThm6Aux

open CJThm6Aux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : G.Connected)
    (T : Finset V) (hT : Even T.card) (hTne : T.Nonempty) :
    (∃ F : Finset (Sym2 V), MetricGenerators.FewComponents.IsMinTJoin G T F ∧ IsConnectedEdgeSet F) ↔
      (IsTreeMetric (fun s t : ↥T => G.dist ↑s ↑t) ∧
        ∀ (N : ℕ) (A : SimpleGraph (Fin N)) (g : ↥T → Fin N),
          IsMinimalRealization (fun s t : ↥T => G.dist ↑s ↑t) A g →
            GraphIsJoin A (Set.range g) ∧
              ∃ φ : Fin N → V, (∀ a b : Fin N, G.dist (φ a) (φ b) = A.dist a b) ∧
                ∀ t : ↥T, φ (g t) = ↑t) := by
  classical
  constructor
  · rintro ⟨F, hFmin, hFconn⟩
    have hTJ := hFmin.1
    obtain ⟨htree, hdistF⟩ := (lemma_2 G hG T F hTJ hFconn).1 hFmin
    set S := edgeSupport F with hSdef
    set H := (edgeGraph F).induce S with hHdef
    have hHc : H.Connected := htree.connected
    have hTS : ∀ t ∈ T, t ∈ S := by
      intro t ht
      have hodd := (hTJ.2 t).2 ht
      have hpos : 0 < edgeDeg F t := hodd.pos
      rw [edgeDeg, Finset.card_pos] at hpos
      obtain ⟨e, he⟩ := hpos
      rw [Finset.mem_filter] at he
      exact ⟨e, he.1, he.2⟩
    have hdistH : ∀ a b : ↥S, H.dist a b = G.dist a.1 b.1 := by
      intro a b
      rw [induce_dist F hHc a b]
      exact hdistF a.1 a.2 b.1 b.2
    set N := Fintype.card ↥S with hN
    set AF := H.overFin hN.symm with hAF
    set ψ : H ≃g AF := H.overFinIso hN.symm with hψ
    set gF : ↥T → Fin N := fun t => ψ ⟨t.1, hTS t.1 t.2⟩ with hgF
    have htreeAF : AF.IsTree := (Iso.isTree_iff ψ).1 htree
    have hdistAF : ∀ a b : ↥S, AF.dist (ψ a) (ψ b) = G.dist a.1 b.1 := by
      intro a b; rw [iso_dist ψ hHc, hdistH]
    have hreal : IsRealization (fun s t : ↥T => G.dist ↑s ↑t) AF gF :=
      ⟨htreeAF, fun s t => hdistAF _ _⟩
    have hdegAF : ∀ b : Fin N, Odd (AF.degree b) ↔ b ∈ Set.range gF := by
      intro b
      obtain ⟨a, rfl⟩ : ∃ a, ψ a = b := ⟨ψ.symm b, by simp⟩
      rw [iso_degree ψ a, degree_eq G F hTJ.1 a, hTJ.2 a.1]
      constructor
      · intro ha; exact ⟨⟨a.1, ha⟩, rfl⟩
      · rintro ⟨t, ht⟩
        have := ψ.injective ht
        rw [← this]; exact t.2
    have hminAF : IsMinimalRealization (fun s t : ↥T => G.dist ↑s ↑t) AF gF := by
      refine ⟨hreal, fun A' hc hsub => ?_⟩
      exact leaf_min AF htreeAF (Set.range gF)
        (fun a h1 => (hdegAF a).1 (by rw [h1]; exact odd_one)) A' hc
        (by rintro _ ⟨x, rfl⟩; exact hsub x)
    have hμ : IsTreeMetric (fun s t : ↥T => G.dist ↑s ↑t) := by
      refine ⟨fun s t h => ?_, N, AF, gF, hreal⟩
      rcases (dist_eq_zero_iff_eq_or_not_reachable).1 h with h' | h'
      · exact Subtype.ext h'
      · exact absurd (hG.preconnected _ _) h'
    refine ⟨hμ, fun N' A g hmin => ?_⟩
    obtain ⟨χ, hχ⟩ := (minimal_realization_unique _ hμ).2 N' A g N AF gF hmin hminAF
    have hAc : A.Connected := hmin.1.1.connected
    refine ⟨fun a => ?_, ⟨fun a => (ψ.symm (χ a)).1, fun a b => ?_, fun t => ?_⟩⟩
    · rw [← iso_degree χ a, hdegAF (χ a)]
      constructor
      · rintro ⟨t, ht⟩
        refine ⟨t, χ.injective ?_⟩
        rw [hχ, ht]
      · rintro ⟨t, rfl⟩
        exact ⟨t, (hχ t).symm⟩
    · rw [← hdistAF, ← iso_dist χ hAc]
      simp
    · simp [hχ, hgF]
  · rintro ⟨hμ, hcond⟩
    obtain ⟨N, A, g, hmin⟩ := (minimal_realization_unique _ hμ).1
    obtain ⟨hjoin, φ, hφ, hext⟩ := hcond N A g hmin
    obtain ⟨hTJ, htree, hdist⟩ :=
      image_of_realization G hG T hTne A hmin.1.1 g hjoin φ hφ hext
    refine ⟨_, (lemma_2 G hG T _ hTJ htree.connected).2 ⟨htree, hdist⟩, htree.connected⟩
