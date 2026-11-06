-- Prove2me | solution 1 for MetricGenerators.ConnectedJoin.image_of_realization
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T20:12:15.795343+00:00
-- url     : https://prove2.me/submissions/ad62e753-f48d-4bc8-b6ba-418c43a3a69f

import Mathlib
import Definitions.Def_MetricGenerators_ConnectedJoin_TJoin
import Definitions.Def_MetricGenerators_ConnectedJoin_TreeMetric

open SimpleGraph MetricGenerators.FewComponents MetricGenerators.ConnectedJoin

namespace CJImageAux

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

theorem degree_inst {α : Type*} (A : SimpleGraph α) (a : α) (i1 i2 : Fintype (A.neighborSet a)) :
    @SimpleGraph.degree α A a i1 = @SimpleGraph.degree α A a i2 := by
  congr; exact Subsingleton.elim _ _

end CJImageAux

open CJImageAux in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hG : G.Connected) (T : Finset V) (hT : T.Nonempty) {N : ℕ} (A : SimpleGraph (Fin N))
    [DecidableRel A.Adj] (hA : A.IsTree) (g : ↥T → Fin N) (hjoin : GraphIsJoin A (Set.range g))
    (φ : Fin N → V) (hφ : ∀ a b : Fin N, G.dist (φ a) (φ b) = A.dist a b)
    (hext : ∀ t : ↥T, φ (g t) = ↑t) :
    MetricGenerators.FewComponents.IsTJoin G T (A.edgeFinset.image (Sym2.map φ)) ∧
      IsTreeEdgeSet (A.edgeFinset.image (Sym2.map φ)) ∧
      ∀ x ∈ MetricGenerators.FewComponents.edgeSupport (A.edgeFinset.image (Sym2.map φ)),
        ∀ y ∈ MetricGenerators.FewComponents.edgeSupport (A.edgeFinset.image (Sym2.map φ)),
          edgeDist (A.edgeFinset.image (Sym2.map φ)) x y = G.dist x y := by
  classical
  set F := A.edgeFinset.image (Sym2.map φ) with hFdef
  have hAc : A.Connected := hA.connected
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := hφ a b
    rw [hab, dist_self] at h
    rcases (dist_eq_zero_iff_eq_or_not_reachable).1 h.symm with h' | h'
    · exact h'
    · exact absurd (hAc a b) h'
  have hsinj : Function.Injective (Sym2.map φ) := Sym2.map.injective hinj
  have hmemF : ∀ a b : Fin N, s(φ a, φ b) ∈ F ↔ A.Adj a b := by
    intro a b
    rw [hFdef, Finset.mem_image]
    constructor
    · rintro ⟨e, he, hee⟩
      have : e = s(a, b) := hsinj (by rw [hee]; simp)
      subst this
      simpa using he
    · intro h
      exact ⟨s(a, b), by simpa using h, by simp⟩
  have hsupp : ∀ v ∈ edgeSupport F, ∃ a, φ a = v := by
    rintro v ⟨e, he, hve⟩
    rw [hFdef, Finset.mem_image] at he
    obtain ⟨e', _, rfl⟩ := he
    obtain ⟨a, _, rfl⟩ := Sym2.mem_map.1 hve
    exact ⟨a, rfl⟩
  -- every vertex of A has a neighbour
  obtain ⟨t0, ht0⟩ := hT
  have hnb : ∀ a : Fin N, ∃ b, A.Adj a b := by
    have h0 : ∃ b, A.Adj (g ⟨t0, ht0⟩) b := by
      have hodd : Odd (A.degree (g ⟨t0, ht0⟩)) := by
        have := (hjoin (g ⟨t0, ht0⟩)).2 ⟨_, rfl⟩
        rwa [degree_inst A _ _ inferInstance] at this
      have hpos := hodd.pos
      rw [← card_neighborFinset_eq_degree, Finset.card_pos] at hpos
      obtain ⟨b, hb⟩ := hpos
      exact ⟨b, by simpa using hb⟩
    intro a
    by_cases ha : a = g ⟨t0, ht0⟩
    · subst ha; exact h0
    · obtain ⟨p⟩ := hAc a (g ⟨t0, ht0⟩)
      have hpn : ¬ p.Nil := fun hn => ha hn.eq
      exact ⟨_, Walk.adj_snd hpn⟩
  have hinS : ∀ a, φ a ∈ edgeSupport F := by
    intro a
    obtain ⟨b, hb⟩ := hnb a
    exact ⟨s(φ a, φ b), (hmemF a b).2 hb, by simp⟩
  set H := (edgeGraph F).induce (edgeSupport F) with hH
  let f : Fin N → ↥(edgeSupport F) := fun a => ⟨φ a, hinS a⟩
  have hfbij : Function.Bijective f := by
    refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun ⟨v, hv⟩ => ?_⟩
    obtain ⟨a, rfl⟩ := hsupp v hv
    exact ⟨a, rfl⟩
  let ψ : A ≃g H :=
    { toEquiv := Equiv.ofBijective f hfbij
      map_rel_iff' := by
        intro a b
        change (edgeGraph F).Adj (φ a) (φ b) ↔ A.Adj a b
        simp only [edgeGraph, fromEdgeSet_adj, Finset.mem_coe, hmemF]
        constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, fun h' => h.ne (hinj h')⟩ }
  have htree : H.IsTree := (Iso.isTree_iff ψ).1 hA
  refine ⟨⟨?_, ?_⟩, htree, ?_⟩
  · intro e he
    rw [Finset.mem_coe, hFdef, Finset.mem_image] at he
    obtain ⟨e', he', rfl⟩ := he
    induction e' using Sym2.ind with
    | _ a b =>
      rw [mem_edgeFinset, mem_edgeSet] at he'
      simp only [Sym2.map_mk, mem_edgeSet]
      rw [← dist_eq_one_iff_adj, hφ, dist_eq_one_iff_adj]
      exact he'
  · intro v
    by_cases hv : ∃ a, φ a = v
    · obtain ⟨a, rfl⟩ := hv
      have hdeg : edgeDeg F (φ a) = A.degree a := by
        rw [edgeDeg, ← card_incidenceFinset_eq_degree, incidenceFinset_eq_filter]
        have : F.filter (fun e => φ a ∈ e) =
            (A.edgeFinset.filter (fun e => a ∈ e)).image (Sym2.map φ) := by
          ext e
          simp only [hFdef, Finset.mem_filter, Finset.mem_image]
          constructor
          · rintro ⟨⟨e', he', rfl⟩, hm⟩
            obtain ⟨a', ha', haa⟩ := Sym2.mem_map.1 hm
            rw [hinj haa] at ha'
            exact ⟨e', ⟨he', ha'⟩, rfl⟩
          · rintro ⟨e', ⟨he', ha'⟩, rfl⟩
            exact ⟨⟨e', he', rfl⟩, Sym2.mem_map.2 ⟨a, ha', rfl⟩⟩
        rw [this, Finset.card_image_of_injective _ hsinj]
      have hj := hjoin a
      rw [hdeg]
      have hdeg' : Odd (A.degree a) ↔ a ∈ Set.range g := by
        convert hj using 2
        exact degree_inst A a _ _
      rw [hdeg']
      constructor
      · rintro ⟨t, rfl⟩; rw [hext]; exact t.2
      · intro ht
        refine ⟨⟨φ a, ht⟩, hinj ?_⟩
        rw [hext]
    · have h0 : edgeDeg F v = 0 := by
        rw [edgeDeg, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro e he hve
        exact hv (hsupp v ⟨e, he, hve⟩)
      rw [h0]
      simp only [Nat.not_odd_zero, false_iff]
      intro ht
      exact hv ⟨g ⟨v, ht⟩, hext _⟩
  · intro x hx y hy
    obtain ⟨a, rfl⟩ := hsupp x hx
    obtain ⟨b, rfl⟩ := hsupp y hy
    rw [edgeDist, hφ]
    have h1 := induce_dist F htree.connected (f a) (f b)
    have h2 := iso_dist ψ hAc a b
    change H.dist (f a) (f b) = A.dist a b at h2
    rw [← h2, h1]
