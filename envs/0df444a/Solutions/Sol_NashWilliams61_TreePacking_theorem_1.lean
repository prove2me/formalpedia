-- Prove2me | solution 1 for NashWilliams61.TreePacking.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-26T13:00:08.44793+00:00
-- url     : https://prove2.me/submissions/f8a68ec0-ce24-484e-8151-6a0effdd6e61

-- SPDX-License-Identifier: Apache-2.0

import Definitions.Def_NashWilliams61_TreePacking_Graphs
import Mathlib


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

def IntersectSubmodular (D : Finset V → ℤ) : Prop :=
  ∀ X Y, (X ∩ Y).Nonempty → D (X ∪ Y) + D (X ∩ Y) ≤ D X + D Y

def outsideMass (g : V → ℤ) (X : Finset V) : ℤ := ∑ v ∈ Finset.univ \ X, g v

def deficiencyGamma (D : Finset V → ℤ) (g : V → ℤ) (s : ℤ)
    (X : Finset V) : ℤ := D X - s + outsideMass g X

theorem outsideMass_eq (g : V → ℤ) (X : Finset V) :
    outsideMass g X = (∑ v, g v) - ∑ v ∈ X, g v := by
  have h := Finset.sum_sdiff (f := g) (Finset.subset_univ X)
  unfold outsideMass
  omega

theorem outsideMass_modular (g : V → ℤ) (X Y : Finset V) :
    outsideMass g (X ∪ Y) + outsideMass g (X ∩ Y) =
      outsideMass g X + outsideMass g Y := by
  simp only [outsideMass_eq]
  have h := Finset.sum_union_inter (f := g) (s₁ := X) (s₂ := Y)
  omega

theorem gamma_submodular {D : Finset V → ℤ} (hD : IntersectSubmodular D)
    (g : V → ℤ) (s : ℤ) : IntersectSubmodular (deficiencyGamma D g s) := by
  intro X Y hXY
  have h := hD X Y hXY
  have hm := outsideMass_modular g X Y
  simp only [deficiencyGamma]
  omega

omit [Fintype V] in
theorem zero_union_inter {D : Finset V → ℤ} (hD : IntersectSubmodular D)
    (hnn : ∀ X, X.Nonempty → 0 ≤ D X) {X Y : Finset V}
    (hXY : (X ∩ Y).Nonempty) (hX : D X = 0) (hY : D Y = 0) :
    D (X ∪ Y) = 0 ∧ D (X ∩ Y) = 0 := by
  have h := hD X Y hXY
  have hi := hnn (X ∩ Y) hXY
  have hu := hnn (X ∪ Y) (hXY.mono (by intro v hv; exact Finset.mem_union_left _ (Finset.mem_inter.mp hv).1))
  omega

theorem least_zero_set {D : Finset V → ℤ}
    (hD : IntersectSubmodular D) (hnn : ∀ X, X.Nonempty → 0 ≤ D X)
    (hmeet : ∀ X Y, X.Nonempty → Y.Nonempty → D X = 0 → D Y = 0 →
      (X ∩ Y).Nonempty)
    (hex : ∃ X, X.Nonempty ∧ D X = 0) :
    ∃ I, I.Nonempty ∧ D I = 0 ∧ ∀ X, X.Nonempty → D X = 0 → I ⊆ X := by
  classical
  let F : Finset (Finset V) := Finset.univ.filter fun X => X.Nonempty ∧ D X = 0
  have hF : F.Nonempty := by
    obtain ⟨X, hX, hDX⟩ := hex
    exact ⟨X, by simp [F, hX, hDX]⟩
  obtain ⟨I, hI, hmin⟩ := F.exists_min_image Finset.card hF
  have hi : I.Nonempty ∧ D I = 0 := by simpa [F] using hI
  refine ⟨I, hi.1, hi.2, ?_⟩
  intro X hX hDX
  have hIX := hmeet I X hi.1 hX hi.2 hDX
  have hz := (zero_union_inter hD hnn hIX hi.2 hDX).2
  have hc := hmin (I ∩ X) (by simp [F, hIX, hz])
  have he : I ∩ X = I := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hc
  exact he ▸ Finset.inter_subset_right

theorem greatest_zero_containing {D : Finset V → ℤ}
    (hD : IntersectSubmodular D) (hnn : ∀ X, X.Nonempty → 0 ≤ D X)
    (v : V) (hsingle : D {v} = 0) :
    ∃ U, v ∈ U ∧ D U = 0 ∧ ∀ X, v ∈ X → D X = 0 → X ⊆ U := by
  classical
  let F : Finset (Finset V) := Finset.univ.filter fun X => v ∈ X ∧ D X = 0
  have hF : F.Nonempty := ⟨{v}, by simp [F, hsingle]⟩
  obtain ⟨U, hU, hmax⟩ := F.exists_max_image Finset.card hF
  have hu : v ∈ U ∧ D U = 0 := by simpa [F] using hU
  refine ⟨U, hu.1, hu.2, ?_⟩
  intro X hvX hDX
  have hUX : (U ∩ X).Nonempty := ⟨v, Finset.mem_inter.mpr ⟨hu.1, hvX⟩⟩
  have hz := (zero_union_inter hD hnn hUX hu.2 hDX).1
  have hc := hmax (U ∪ X) (by simp [F, hu.1, hz])
  have he : U = U ∪ X := Finset.eq_of_subset_of_card_le Finset.subset_union_left hc
  exact he.symm ▸ Finset.subset_union_right

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [DecidableEq V] [Fintype E]

omit [DecidableEq V] in
theorem mem_edgesIn_iff (ends : E → Sym2 V) (X : Finset V) (e : E) :
    e ∈ edgesIn ends X ↔ ∀ v ∈ ends e, v ∈ X := by
  classical
  simp [edgesIn]

omit [DecidableEq V] in
theorem edgesIn_mono (ends : E → Sym2 V) {X Y : Finset V} (hXY : X ⊆ Y) :
    edgesIn ends X ⊆ edgesIn ends Y := by
  intro e he
  exact (mem_edgesIn_iff ends Y e).mpr (fun v hv => hXY ((mem_edgesIn_iff ends X e).mp he v hv))

theorem edgesIn_inter [DecidableEq E] (ends : E → Sym2 V) (X Y : Finset V) :
    edgesIn ends (X ∩ Y) = edgesIn ends X ∩ edgesIn ends Y := by
  classical
  ext e
  simp only [mem_edgesIn_iff, Finset.mem_inter]
  constructor
  · intro h
    exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩
  · rintro ⟨hX, hY⟩ v hv
    exact ⟨hX v hv, hY v hv⟩

theorem edgesIn_card_supermodular (ends : E → Sym2 V) (X Y : Finset V) :
    ((edgesIn ends X).card : ℤ) + (edgesIn ends Y).card ≤
      (edgesIn ends (X ∪ Y)).card + (edgesIn ends (X ∩ Y)).card := by
  classical
  have hsubset : edgesIn ends X ∪ edgesIn ends Y ⊆ edgesIn ends (X ∪ Y) := by
    apply Finset.union_subset
    · exact edgesIn_mono ends Finset.subset_union_left
    · exact edgesIn_mono ends Finset.subset_union_right
  have hle := Finset.card_le_card hsubset
  have he := Finset.card_union_add_card_inter (edgesIn ends X) (edgesIn ends Y)
  rw [edgesIn_inter]
  omega

theorem delta_submodular (k : ℕ) (ends : E → Sym2 V) :
    IntersectSubmodular (Delta k ends) := by
  intro X Y _
  have h := edgesIn_card_supermodular ends X Y
  have hc : ((X ∪ Y).card : ℤ) + (X ∩ Y).card = (X.card : ℤ) + Y.card := by
    exact_mod_cast Finset.card_union_add_card_inter X Y
  simp only [Delta]
  nlinarith

omit [DecidableEq V] in
theorem edgesIn_singleton_eq_empty (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) : edgesIn ends {v} = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  apply hloop e
  have h := (mem_edgesIn_iff ends {v} e).mp he
  have hall : ∀ p : Sym2 V, (∀ w ∈ p, w ∈ ({v} : Finset V)) → p.IsDiag := by
    intro p
    refine Sym2.inductionOn p ?_
    intro a b hab
    have ha := hab a (Sym2.mem_mk_left a b)
    have hb := hab b (Sym2.mem_mk_right a b)
    simp only [Finset.mem_singleton] at ha hb
    exact Sym2.mk_isDiag_iff.mpr (ha.trans hb.symm)
  exact hall (ends e) h

omit [DecidableEq V] in
theorem delta_singleton (k : ℕ) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) : Delta k ends {v} = 0 := by
  simp [Delta, edgesIn_singleton_eq_empty ends hloop]

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn
namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [DecidableEq E] (ends : E → Sym2 V)

omit [DecidableEq E] in
theorem edgeGraph_adj_iff (F : Finset E) (u v : V) :
    (edgeGraph ends F).Adj u v ↔ (∃ e ∈ F, ends e = s(u, v)) ∧ u ≠ v := by
  simp only [edgeGraph, SimpleGraph.fromEdgeSet_adj, Set.mem_image, Finset.mem_coe]

omit [DecidableEq E] in
theorem edgeGraph_mono {F H : Finset E} (h : F ⊆ H) :
    edgeGraph ends F ≤ edgeGraph ends H := by
  apply SimpleGraph.fromEdgeSet_mono
  exact Set.image_mono h

theorem forest_empty : IsForest ends ∅ := by
  intro e he
  simp at he

theorem forest_mono {F H : Finset E} (h : F ⊆ H) (hf : IsForest ends H) :
    IsForest ends F := by
  intro e he u v huv hr
  exact hf e (h he) u v huv (hr.mono (edgeGraph_mono ends (Finset.erase_subset_erase e h)))

theorem forest_endpoints_ne {F : Finset E} (hf : IsForest ends F)
    {e : E} (he : e ∈ F) {u v : V} (huv : ends e = s(u, v)) : u ≠ v := by
  intro h
  subst v
  exact hf e he u u huv SimpleGraph.Reachable.rfl

theorem forest_ends_injOn {F : Finset E} (hf : IsForest ends F) :
    Set.InjOn ends (F : Set E) := by
  intro e he f hf' hef
  by_contra hne
  have hex : ∃ u v, ends e = s(u, v) := by
    induction ends e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, rfl⟩
  obtain ⟨u, v, huv'⟩ := hex
  apply hf e he u v huv'
  apply SimpleGraph.Adj.reachable
  rw [edgeGraph_adj_iff]
  exact ⟨⟨f, Finset.mem_erase.mpr ⟨Ne.symm hne, hf'⟩, hef.symm.trans huv'⟩,
    forest_endpoints_ne ends hf he huv'⟩

theorem delete_edge_le_erase {F : Finset E} {e : E} {u v : V}
    (he : ends e = s(u, v)) :
    (edgeGraph ends F).deleteEdges {s(u, v)} ≤ edgeGraph ends (F.erase e) := by
  intro a b hab
  obtain ⟨hab, hnot⟩ := SimpleGraph.deleteEdges_adj.mp hab
  obtain ⟨⟨f, hf, hfab⟩, hne⟩ := (edgeGraph_adj_iff ends F a b).mp hab
  apply (edgeGraph_adj_iff ends (F.erase e) a b).mpr
  refine ⟨⟨f, Finset.mem_erase.mpr ⟨?_, hf⟩, hfab⟩, hne⟩
  intro hfe
  subst f
  exact hnot (Set.mem_singleton_iff.mpr (hfab.symm.trans he))

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn
namespace NashWilliams61.TreePacking.NWFresh
variable {V E F : Type*} [DecidableEq E] [DecidableEq F]

omit [DecidableEq E] in
theorem edgeGraph_image (ends : E → Sym2 V) (ends' : F → Sym2 V)
    (f : E → F) (hf : ∀ e, ends' (f e) = ends e) (T : Finset E) :
    edgeGraph ends' (T.image f) = edgeGraph ends T := by
  classical
  unfold edgeGraph
  congr 1
  rw [Finset.coe_image, ← Set.image_comp]
  congr 1
  funext e
  exact hf e

theorem forest_image (ends : E → Sym2 V) (ends' : F → Sym2 V)
    (f : E → F) (hi : Function.Injective f) (hf : ∀ e, ends' (f e) = ends e)
    {T : Finset E} (ht : IsForest ends T) : IsForest ends' (T.image f) := by
  classical
  intro e he u v hev hr
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  have herase : (T.image f).erase (f a) = (T.erase a).image f := by
    ext b
    simp only [Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨hb, c, hc, rfl⟩
      exact ⟨c, ⟨fun h => hb (congrArg f h), hc⟩, rfl⟩
    · rintro ⟨c, ⟨hca, hc⟩, rfl⟩
      exact ⟨fun h => hca (hi h), c, hc, rfl⟩
  rw [herase, edgeGraph_image ends ends' f hf] at hr
  exact ht a ha u v ((hf a).symm.trans hev) hr

theorem forest_of_image (ends : E → Sym2 V) (ends' : F → Sym2 V)
    (f : E → F) (hi : Function.Injective f) (hf : ∀ e, ends' (f e) = ends e)
    {T : Finset E} (ht : IsForest ends' (T.image f)) : IsForest ends T := by
  intro a ha u v huv hr
  apply ht (f a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩) u v ((hf a).trans huv)
  have hsub : (T.erase a).image f ⊆ (T.image f).erase (f a) := by
    intro b hb
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨hca, hc⟩ := Finset.mem_erase.mp hc
    exact Finset.mem_erase.mpr ⟨fun h => hca (hi h), Finset.mem_image.mpr ⟨c, hc, rfl⟩⟩
  rw [← edgeGraph_image ends ends' f hf (T.erase a)] at hr
  exact hr.mono (edgeGraph_mono ends' hsub)

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V W E : Type*} [DecidableEq E]

omit [DecidableEq E] in
theorem edgeGraph_map_adj (ends : E → Sym2 V) (f : V → W)
    (hi : Function.Injective f) (T : Finset E) {u v : V}
    (h : (edgeGraph ends T).Adj u v) :
    (edgeGraph (fun e => Sym2.map f (ends e)) T).Adj (f u) (f v) := by
  obtain ⟨⟨e, he, hev⟩, hne⟩ := (edgeGraph_adj_iff ends T u v).mp h
  apply (edgeGraph_adj_iff _ T _ _).mpr
  refine ⟨⟨e, he, ?_⟩, fun h => hne (hi h)⟩
  simp only [hev, Sym2.map_mk]

def vertexMapHom (ends : E → Sym2 V) (f : V → W)
    (hi : Function.Injective f) (T : Finset E) :
    edgeGraph ends T →g edgeGraph (fun e => Sym2.map f (ends e)) T where
  toFun := f
  map_rel' := edgeGraph_map_adj ends f hi T

omit [DecidableEq E] in
theorem reachable_vertex_map (ends : E → Sym2 V) (f : V → W)
    (hi : Function.Injective f) (T : Finset E) {u v : V}
    (h : (edgeGraph ends T).Reachable u v) :
    (edgeGraph (fun e => Sym2.map f (ends e)) T).Reachable (f u) (f v) :=
  h.map (vertexMapHom ends f hi T)

def vertexInverseHom (ends : E → Sym2 V) (f : V → W) (g : W → V)
    (hg : Function.LeftInverse g f) (T : Finset E) :
    edgeGraph (fun e => Sym2.map f (ends e)) T →g edgeGraph ends T where
  toFun := g
  map_rel' := by
    intro u v h
    obtain ⟨⟨e, he, hev⟩, hne⟩ := (edgeGraph_adj_iff _ T u v).mp h
    have hex : ∃ a b, ends e = s(a, b) := by
      induction ends e using Sym2.inductionOn with
      | _ a b => exact ⟨a, b, rfl⟩
    obtain ⟨a, b, hab⟩ := hex
    simp only [hab, Sym2.map_mk] at hev
    have hh : (f a = u ∧ f b = v) ∨ (f a = v ∧ f b = u) := by simpa using hev
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · apply (edgeGraph_adj_iff ends T _ _).mpr
      rw [hg a, hg b]
      exact ⟨⟨e, he, hab⟩, fun h => hne (congrArg f h)⟩
    · apply (edgeGraph_adj_iff ends T _ _).mpr
      rw [hg a, hg b]
      exact ⟨⟨e, he, hab.trans Sym2.eq_swap⟩, fun h => hne (congrArg f h)⟩

theorem forest_vertex_map (ends : E → Sym2 V) (f : V → W) (g : W → V)
    (hg : Function.LeftInverse g f) {T : Finset E} (ht : IsForest ends T) :
    IsForest (fun e => Sym2.map f (ends e)) T := by
  intro e he u v hev hr
  have hh := congrArg (Sym2.map g) hev
  have hi : Sym2.map g (Sym2.map f (ends e)) = ends e := by
    induction ends e using Sym2.inductionOn with
    | _ a b => simp only [Sym2.map_mk, hg a, hg b]
  rw [hi, Sym2.map_mk] at hh
  exact ht e he (g u) (g v) hh (hr.map (vertexInverseHom ends f g hg (T.erase e)))

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical NagamochiIbaraki.EdgeConn
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [DecidableEq V] [Fintype E]

abbrev InternalEdge (ends : E → Sym2 V) (X : Finset V) := {e // e ∈ edgesIn ends X}

def restrictedEnds (ends : E → Sym2 V) (X : Finset V) : InternalEdge ends X → Sym2 X :=
  fun e => (ends e.val).pmap Subtype.mk ((mem_edgesIn_iff ends X e.val).mp e.property)

omit [DecidableEq V] in
theorem restrictedEnds_map (ends : E → Sym2 V) (X : Finset V) (e : InternalEdge ends X) :
    Sym2.map Subtype.val (restrictedEnds ends X e) = ends e.val :=
  Sym2.pmap_subtype_map_subtypeVal _ _

omit [DecidableEq V] in
theorem restrictedEnds_mem (ends : E → Sym2 V) (X : Finset V)
    (e : InternalEdge ends X) (v : X) : v ∈ restrictedEnds ends X e ↔ v.val ∈ ends e.val := by
  rw [← restrictedEnds_map ends X e, Sym2.mem_map]
  constructor
  · exact fun h => ⟨v, h, rfl⟩
  · rintro ⟨w, hw, hh⟩
    exact (Subtype.ext hh : w = v) ▸ hw

omit [DecidableEq V] in
theorem restrictedEnds_loopless (ends : E → Sym2 V) (hl : ∀ e, ¬ (ends e).IsDiag)
    (X : Finset V) : ∀ e, ¬ (restrictedEnds ends X e).IsDiag := by
  intro e he
  apply hl e.val
  rw [← restrictedEnds_map ends X e]
  exact Sym2.IsDiag.map he

def liftInternalSet (X : Finset V) (Y : Finset X) : Finset V :=
  Y.map ⟨Subtype.val, Subtype.val_injective⟩

omit [DecidableEq V] in
theorem internal_edges_lift (ends : E → Sym2 V) (X : Finset V) (Y : Finset X) :
    (edgesIn (restrictedEnds ends X) Y).image Subtype.val = edgesIn ends (liftInternalSet X Y) := by
  ext e
  constructor
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    rw [mem_edgesIn_iff] at ha ⊢
    intro v hv
    have hvX : v ∈ X := (mem_edgesIn_iff ends X a.val).mp a.property v hv
    exact Finset.mem_map.mpr ⟨⟨v, hvX⟩, ha _ ((restrictedEnds_mem ends X a _).mpr hv), rfl⟩
  · intro he
    have heX : e ∈ edgesIn ends X := by
      apply edgesIn_mono ends _ he
      intro v hv
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hv
      exact a.property
    refine Finset.mem_image.mpr ⟨⟨e, heX⟩, ?_, rfl⟩
    rw [mem_edgesIn_iff] at he ⊢
    intro v hv
    obtain ⟨a, ha, hh⟩ := Finset.mem_map.mp (he v.val ((restrictedEnds_mem ends X _ v).mp hv))
    exact (Subtype.ext hh : a = v) ▸ ha

omit [DecidableEq V] in
theorem internal_edges_card (ends : E → Sym2 V) (X : Finset V) (Y : Finset X) :
    (edgesIn (restrictedEnds ends X) Y).card = (edgesIn ends (liftInternalSet X Y)).card := by
  rw [← internal_edges_lift, Finset.card_image_of_injective _ Subtype.val_injective]

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [DecidableEq E] (ends : E → Sym2 V)

theorem forest_isAcyclic {F : Finset E} (hf : IsForest ends F) :
    (edgeGraph ends F).IsAcyclic := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge]
  intro u v huv
  obtain ⟨⟨e, he, hev⟩, _⟩ := (edgeGraph_adj_iff ends F u v).mp huv
  rw [SimpleGraph.isBridge_iff]
  intro hr
  exact hf e he u v hev (hr.mono (delete_edge_le_erase ends hev))

theorem erase_le_delete_edge {F : Finset E} (hi : Set.InjOn ends (F : Set E))
    {e : E} (he : e ∈ F) {u v : V} (hev : ends e = s(u, v)) :
    edgeGraph ends (F.erase e) ≤ (edgeGraph ends F).deleteEdges {s(u, v)} := by
  intro a b hab
  obtain ⟨⟨f, hf, hfab⟩, hne⟩ := (edgeGraph_adj_iff ends (F.erase e) a b).mp hab
  obtain ⟨hfe, hf⟩ := Finset.mem_erase.mp hf
  apply SimpleGraph.deleteEdges_adj.mpr
  refine ⟨(edgeGraph_adj_iff ends F a b).mpr ⟨⟨f, hf, hfab⟩, hne⟩, ?_⟩
  intro hh
  have hh' : s(a, b) = s(u, v) := Set.mem_singleton_iff.mp hh
  exact hfe (hi hf he (hfab.trans (hh'.trans hev.symm)))

theorem forest_of_injective_acyclic {F : Finset E}
    (hi : Set.InjOn ends (F : Set E))
    (hl : ∀ e ∈ F, ¬ (ends e).IsDiag) (ha : (edgeGraph ends F).IsAcyclic) :
    IsForest ends F := by
  intro e he u v hev hr
  have hne : u ≠ v := by
    intro h
    subst v
    exact hl e he (by simp [hev])
  have hadj : (edgeGraph ends F).Adj u v :=
    (edgeGraph_adj_iff ends F u v).mpr ⟨⟨e, he, hev⟩, hne⟩
  have hb := (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp ha) hadj
  rw [SimpleGraph.isBridge_iff] at hb
  exact hb (hr.mono (erase_le_delete_edge ends hi he hev))

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [DecidableEq E] (ends : E → Sym2 V)

theorem edgeGraph_insert (F : Finset E) (e : E) {u v : V} (he : ends e = s(u, v)) :
    edgeGraph ends (insert e F) = edgeGraph ends F ⊔ SimpleGraph.edge u v := by
  unfold edgeGraph SimpleGraph.edge
  rw [← SimpleGraph.fromEdgeSet_union]
  congr 1
  simp only [Finset.coe_insert, Set.image_insert_eq, he, Set.union_singleton]

theorem forest_loopless {F : Finset E} (hf : IsForest ends F) :
    ∀ e ∈ F, ¬ (ends e).IsDiag := by
  intro e he
  have hex : ∃ u v, ends e = s(u, v) := by
    induction ends e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, rfl⟩
  obtain ⟨u, v, huv⟩ := hex
  simpa [huv] using forest_endpoints_ne ends hf he huv

theorem forest_insert_of_not_reachable {F : Finset E} (hf : IsForest ends F)
    {e : E} {u v : V} (he : ends e = s(u, v))
    (hn : ¬ (edgeGraph ends F).Reachable u v) : IsForest ends (insert e F) := by
  have huv : u ≠ v := by
    intro h
    subst v
    exact hn SimpleGraph.Reachable.rfl
  have hnew : ∀ f ∈ F, ends f ≠ ends e := by
    intro f hf' hh
    exact hn ((edgeGraph_adj_iff ends F u v).mpr ⟨⟨f, hf', hh.trans he⟩, huv⟩).reachable
  apply forest_of_injective_acyclic ends
  · intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact (hnew b hb hab.symm).elim
    · rcases hb with rfl | hb
      · exact (hnew a ha hab).elim
      · exact forest_ends_injOn ends hf ha hb hab
  · intro f hf'
    rcases Finset.mem_insert.mp hf' with rfl | hf'
    · simpa [he] using huv
    · exact forest_loopless ends hf f hf'
  · rw [edgeGraph_insert ends F e he]
    exact (forest_isAcyclic ends hf).sup_edge_of_not_reachable hn

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [DecidableEq E] (ends : E → Sym2 V)

theorem reachable_of_adj_reachable {G H : SimpleGraph V}
    (h : ∀ u v, G.Adj u v → H.Reachable u v) {u v : V} (hr : G.Reachable u v) :
    H.Reachable u v := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons a b c hab p ih => exact (h a b hab).trans ih

theorem exists_forest_extension {F H : Finset E} (hFH : F ⊆ H)
    (hf : IsForest ends F) :
    ∃ T, F ⊆ T ∧ T ⊆ H ∧ IsForest ends T ∧
      (edgeGraph ends T).Reachable = (edgeGraph ends H).Reachable := by
  classical
  let S := H.powerset.filter (fun T => F ⊆ T ∧ IsForest ends T)
  have hS : S.Nonempty := ⟨F, by simp [S, hFH, hf]⟩
  obtain ⟨T, hT, hmax⟩ := S.exists_max_image Finset.card hS
  obtain ⟨hTH, hFT, ht⟩ : T ⊆ H ∧ F ⊆ T ∧ IsForest ends T := by
    simpa [S] using hT
  refine ⟨T, hFT, hTH, ht, ?_⟩
  funext u v
  apply propext
  constructor
  · exact fun hr => hr.mono (edgeGraph_mono ends hTH)
  · apply reachable_of_adj_reachable
    intro a b hab
    by_contra hn
    obtain ⟨⟨e, he, hev⟩, _⟩ := (edgeGraph_adj_iff ends H a b).mp hab
    have hen : e ∉ T := by
      intro het
      exact hn ((edgeGraph_adj_iff ends T a b).mpr
        ⟨⟨e, het, hev⟩, hab.ne⟩).reachable
    have hins : insert e T ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.insert_subset he hTH,
        hFT.trans (Finset.subset_insert e T), forest_insert_of_not_reachable ends ht hev hn⟩
    have hc := hmax _ hins
    rw [Finset.card_insert_of_notMem hen] at hc
    omega

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq E] (ends : E → Sym2 V)

omit [DecidableEq E] in
theorem edgeFinset_eq_image (F : Finset E) (hl : ∀ e ∈ F, ¬ (ends e).IsDiag) :
    (edgeGraph ends F).edgeFinset = F.image ends := by
  classical
  ext e
  rw [SimpleGraph.mem_edgeFinset]
  simp only [edgeGraph, SimpleGraph.edgeSet_fromEdgeSet, Set.mem_sdiff,
    Set.mem_image, Finset.mem_coe, Finset.mem_image]
  constructor
  · exact And.left
  · rintro ⟨f, hf, rfl⟩
    exact ⟨⟨f, hf, rfl⟩, hl f hf⟩

theorem forest_edgeFinset_card {F : Finset E} (hf : IsForest ends F) :
    (edgeGraph ends F).edgeFinset.card = F.card := by
  classical
  rw [edgeFinset_eq_image ends F (forest_loopless ends hf)]
  exact Finset.card_image_of_injOn (forest_ends_injOn ends hf)

theorem spanningTree_simple [Fintype E] {T : Finset E} (ht : IsSpanningTree ends T) :
    (edgeGraph ends T).IsTree := by
  obtain ⟨_, hne, _, hf, hc⟩ := ht
  have : Nonempty V := ⟨hne.choose⟩
  exact ⟨⟨fun u v => hc u (Finset.mem_univ u) v (Finset.mem_univ v)⟩,
    forest_isAcyclic ends hf⟩

theorem spanningTree_card [Fintype E] {T : Finset E} (ht : IsSpanningTree ends T) :
    T.card + 1 = Fintype.card V := by
  have hc := (spanningTree_simple ends ht).card_edgeFinset
  rw [forest_edgeFinset_card ends ht.2.2.2.1] at hc
  exact hc

theorem connected_exists_forest_tree [Nonempty V] {H F : Finset E}
    (hFH : F ⊆ H) (hf : IsForest ends F) (hc : (edgeGraph ends H).Connected) :
    ∃ T, F ⊆ T ∧ T ⊆ H ∧ IsTreeOn ends Finset.univ T := by
  obtain ⟨T, hFT, hTH, ht, hr⟩ := exists_forest_extension ends hFH hf
  refine ⟨T, hFT, hTH, Finset.univ_nonempty, ?_, ht, ?_⟩
  · exact fun _ _ v _ => Finset.mem_univ v
  · intro u _ v _
    rw [hr]
    exact hc u v

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

theorem treeOn_univ_iff (ends : E → Sym2 V) (T : Finset E) :
    IsTreeOn ends Finset.univ T ↔ IsSpanningTree ends T := by
  exact ⟨fun h => ⟨Finset.subset_univ T, h⟩, And.right⟩

theorem connected_edge_count [Nonempty V] (ends : E → Sym2 V) (H : Finset E)
    (hc : (edgeGraph ends H).Connected) : Fintype.card V ≤ H.card + 1 := by
  obtain ⟨T, _, hTH, ht⟩ := connected_exists_forest_tree ends
    (Finset.empty_subset H) (forest_empty ends) hc
  have hcard := spanningTree_card ends ((treeOn_univ_iff ends T).mp ht)
  have hle := Finset.card_le_card hTH
  omega

theorem tree_of_connected_card [Nonempty V] (ends : E → Sym2 V) (H : Finset E)
    (hc : (edgeGraph ends H).Connected) (hcard : H.card + 1 = Fintype.card V) :
    IsSpanningTree ends H := by
  obtain ⟨T, _, hTH, ht⟩ := connected_exists_forest_tree ends
    (Finset.empty_subset H) (forest_empty ends) hc
  have hT := spanningTree_card ends ((treeOn_univ_iff ends T).mp ht)
  have heq : T = H := Finset.eq_of_subset_of_card_le hTH (by omega)
  subst T
  exact (treeOn_univ_iff ends H).mp ht

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

theorem crossing_mk_iff (ends : E → Sym2 V) (P : Finpartition (Finset.univ : Finset V))
    {e : E} {u v : V} (he : ends e = s(u, v)) :
    e ∈ crossing ends P ↔ P.part u ≠ P.part v := by
  simp only [crossing, Finset.mem_filter, Finset.mem_univ, true_and, he]
  constructor
  · rintro ⟨a, b, hab, hn⟩
    have hh : (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by simpa using hab
    rcases hh with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hn
    · exact Ne.symm hn
  · exact fun h => ⟨u, v, rfl, h⟩

theorem internal_indicator_sum (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (e : E) :
    (∑ X ∈ P.parts, if e ∈ edgesIn ends X then (1 : ℕ) else 0) +
      (if e ∈ crossing ends P then 1 else 0) = 1 := by
  have hex : ∃ u v, ends e = s(u, v) := by
    induction ends e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, rfl⟩
  obtain ⟨u, v, he⟩ := hex
  simp only [crossing_mk_iff ends P he]
  have hm : P.part u ∈ P.parts := P.part_mem.mpr (Finset.mem_univ u)
  have hu : u ∈ P.part u := P.mem_part_self.mpr (Finset.mem_univ u)
  by_cases h : P.part u = P.part v
  · rw [if_neg (not_not.mpr h)]
    have hv : v ∈ P.part u := h ▸ P.mem_part_self.mpr (Finset.mem_univ v)
    rw [Finset.sum_eq_single (P.part u)]
    · simp [mem_edgesIn_iff, he, hu, hv]
    · intro X hX hXne
      have hno : e ∉ edgesIn ends X := by
        intro heX
        have huX : u ∈ X := (mem_edgesIn_iff ends X e).mp heX u (by simp [he])
        exact hXne (P.part_eq_of_mem hX huX).symm
      simp [hno]
    · exact fun hn => (hn hm).elim
  · rw [if_pos h]
    have hz : ∀ X ∈ P.parts, e ∉ edgesIn ends X := by
      intro X hX heX
      have hx := (mem_edgesIn_iff ends X e).mp heX
      exact h ((P.part_eq_of_mem hX (hx u (by simp [he]))).trans
        (P.part_eq_of_mem hX (hx v (by simp [he]))).symm)
    have hs : (∑ X ∈ P.parts, if e ∈ edgesIn ends X then (1 : ℕ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro X hX
      simp only [if_neg (hz X hX)]
    rw [hs]

theorem partition_edge_count (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (∑ X ∈ P.parts, (edgesIn ends X).card) + (crossing ends P).card = Fintype.card E := by
  have h := congrArg (fun f : E → ℕ => ∑ e, f e) (funext (internal_indicator_sum ends P))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, mul_one] at h
  rw [Finset.sum_comm] at h
  have hi (S : Finset E) : (∑ e : E, if e ∈ S then (1 : ℕ) else 0) = S.card := by
    simp
  simpa only [hi] using h

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev PartitionVertex (P : Finpartition (Finset.univ : Finset V)) := {X // X ∈ P.parts}

noncomputable def partitionVertex (P : Finpartition (Finset.univ : Finset V)) (v : V) :
    PartitionVertex P := ⟨P.part v, P.part_mem.mpr (Finset.mem_univ v)⟩

noncomputable def quotientEnds (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (e : E) : Sym2 (PartitionVertex P) :=
  Sym2.map (partitionVertex P) (ends e)

theorem partitionVertex_surjective (P : Finpartition (Finset.univ : Finset V)) :
    Function.Surjective (partitionVertex P) := by
  intro X
  obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts X.property
  exact ⟨v, Subtype.ext (P.part_eq_of_mem X.property hv)⟩

theorem reachable_map_of_edges {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B}
    (f : A → B) (hf : ∀ a b, G.Adj a b → H.Reachable (f a) (f b))
    {a b : A} (hr : G.Reachable a b) : H.Reachable (f a) (f b) := by
  obtain ⟨p⟩ := hr
  induction p with
  | nil => exact SimpleGraph.Reachable.rfl
  | @cons a b c hab p ih => exact (hf a b hab).trans ih

theorem quotient_reachable (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (T : Finset E)
    {u v : V} (hr : (edgeGraph ends T).Reachable u v) :
    (edgeGraph (quotientEnds ends P) (T.filter (· ∈ crossing ends P))).Reachable
      (partitionVertex P u) (partitionVertex P v) := by
  apply reachable_map_of_edges (partitionVertex P) _ hr
  intro a b hab
  by_cases heq : partitionVertex P a = partitionVertex P b
  · rw [heq]
  · obtain ⟨⟨e, he, hev⟩, _⟩ := (edgeGraph_adj_iff ends T a b).mp hab
    apply SimpleGraph.Adj.reachable
    apply (edgeGraph_adj_iff _ _ _ _).mpr
    refine ⟨⟨e, Finset.mem_filter.mpr ⟨he, ?_⟩, ?_⟩, heq⟩
    · apply (crossing_mk_iff ends P hev).mpr
      exact fun hh => heq (Subtype.ext hh)
    · simp only [quotientEnds, hev, Sym2.map_mk]

theorem quotient_connected (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (T : Finset E)
    (hc : (edgeGraph ends T).Connected) :
    (edgeGraph (quotientEnds ends P) (T.filter (· ∈ crossing ends P))).Connected := by
  have : Nonempty V := hc.nonempty
  have : Nonempty (PartitionVertex P) := ⟨partitionVertex P (Classical.arbitrary V)⟩
  constructor
  intro X Y
  obtain ⟨u, rfl⟩ := partitionVertex_surjective P X
  obtain ⟨v, rfl⟩ := partitionVertex_surjective P Y
  exact quotient_reachable ends P T (hc u v)

theorem tree_crossing_card (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) {T : Finset E}
    (ht : IsSpanningTree ends T) :
    P.parts.card ≤ (T.filter (· ∈ crossing ends P)).card + 1 := by
  have hc := quotient_connected ends P T (spanningTree_simple ends ht).connected
  have : Nonempty (PartitionVertex P) := hc.nonempty
  simpa only [Fintype.card_coe] using connected_edge_count (quotientEnds ends P) _ hc

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V Q : Type*} [Fintype V] [DecidableEq V] [Fintype Q]

noncomputable def fiberPartition (f : V → Q) : Finpartition (Finset.univ : Finset V) :=
  Finpartition.ofSetoid (Setoid.ker f)

omit [Fintype Q] in
theorem fiberPartition_part_eq (f : V → Q) (u v : V) :
    (fiberPartition f).part u = (fiberPartition f).part v ↔ f u = f v := by
  rw [← (fiberPartition f).mem_part_iff_part_eq_part (Finset.mem_univ u) (Finset.mem_univ v)]
  rw [fiberPartition, Finpartition.mem_part_ofSetoid_iff_rel]
  exact eq_comm

theorem fiberPartition_card (f : V → Q) (hf : Function.Surjective f) :
    (fiberPartition f).parts.card = Fintype.card Q := by
  let g : Q → PartitionVertex (fiberPartition f) := fun q =>
    partitionVertex (fiberPartition f) (hf q).choose
  have hg : Function.Bijective g := by
    constructor
    · intro a b hab
      have hh := (fiberPartition_part_eq f _ _).mp (congrArg Subtype.val hab)
      simpa only [(hf a).choose_spec, (hf b).choose_spec] using hh
    · intro X
      obtain ⟨v, hv⟩ := partitionVertex_surjective (fiberPartition f) X
      refine ⟨f v, ?_⟩
      rw [← hv]
      apply Subtype.ext
      exact (fiberPartition_part_eq f _ _).mpr (hf (f v)).choose_spec
  have hc := Fintype.card_of_bijective hg
  simpa only [Fintype.card_coe] using hc.symm

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev CrossingEdge (ends : E → Sym2 V) (P : Finpartition (Finset.univ : Finset V)) :=
  {e // e ∈ crossing ends P}
noncomputable def quotientNativeEnds (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (e : CrossingEdge ends P) :=
  quotientEnds ends P e.val

noncomputable def coarsePartition (P : Finpartition (Finset.univ : Finset V))
    (R : Finpartition (Finset.univ : Finset (PartitionVertex P))) :=
  fiberPartition (partitionVertex R ∘ partitionVertex P)

theorem coarsePartition_card (P : Finpartition (Finset.univ : Finset V))
    (R : Finpartition (Finset.univ : Finset (PartitionVertex P))) :
    (coarsePartition P R).parts.card = R.parts.card := by
  rw [coarsePartition, fiberPartition_card _
    ((partitionVertex_surjective R).comp (partitionVertex_surjective P))]
  exact Fintype.card_coe R.parts

omit [DecidableEq E] in
theorem coarse_crossing_sub (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (R : Finpartition (Finset.univ : Finset (PartitionVertex P))) :
    crossing ends (coarsePartition P R) ⊆ crossing ends P := by
  intro e he
  have hex : ∃ u v, ends e = s(u, v) := by
    induction ends e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, rfl⟩
  obtain ⟨u, v, hev⟩ := hex
  rw [crossing_mk_iff ends _ hev] at he ⊢
  intro hh
  apply he
  apply (fiberPartition_part_eq _ _ _).mpr
  exact congrArg (partitionVertex R) (Subtype.ext hh)

omit [DecidableEq E] in
theorem quotient_crossing_iff (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (R : Finpartition (Finset.univ : Finset (PartitionVertex P)))
    (e : CrossingEdge ends P) :
    e ∈ crossing (quotientNativeEnds ends P) R ↔
      e.val ∈ crossing ends (coarsePartition P R) := by
  have hex : ∃ u v, ends e.val = s(u, v) := by
    induction ends e.val using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, rfl⟩
  obtain ⟨u, v, hev⟩ := hex
  have hq : quotientNativeEnds ends P e = s(partitionVertex P u, partitionVertex P v) := by
    simp only [quotientNativeEnds, quotientEnds, hev, Sym2.map_mk]
  rw [crossing_mk_iff _ R hq, crossing_mk_iff ends _ hev]
  have hh : (coarsePartition P R).part u = (coarsePartition P R).part v ↔
      R.part (partitionVertex P u) = R.part (partitionVertex P v) := by
    change (fiberPartition (partitionVertex R ∘ partitionVertex P)).part u =
      (fiberPartition (partitionVertex R ∘ partitionVertex P)).part v ↔ _
    rw [fiberPartition_part_eq]
    exact Subtype.ext_iff
  exact not_congr hh.symm

theorem quotient_crossing_card (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (R : Finpartition (Finset.univ : Finset (PartitionVertex P))) :
    (crossing (quotientNativeEnds ends P) R).card =
      (crossing ends (coarsePartition P R)).card := by
  have heq : (crossing (quotientNativeEnds ends P) R).image Subtype.val =
      crossing ends (coarsePartition P R) := by
    ext e
    constructor
    · rintro he
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
      exact (quotient_crossing_iff ends P R a).mp ha
    · intro he
      exact Finset.mem_image.mpr ⟨⟨e, coarse_crossing_sub ends P R he⟩,
        (quotient_crossing_iff ends P R _).mpr he, rfl⟩
  rw [← heq, Finset.card_image_of_injective _ Subtype.val_injective]

theorem quotient_admissible (k : ℕ) (ends : E → Sym2 V)
    (ha : IsAdmissible k ends) (P : Finpartition (Finset.univ : Finset V)) :
    IsAdmissible k (quotientNativeEnds ends P) := by
  intro R
  have h := ha (coarsePartition P R)
  change (k : ℤ) * ((R.parts.card : ℤ) - 1) ≤ _
  rw [quotient_crossing_card]
  simpa only [IsAdmissiblePartition, coarsePartition_card] using h

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

def internalImage (ends : E → Sym2 V) (X : Finset V) (T : Finset (InternalEdge ends X)) :
    Finset E := T.image Subtype.val

omit [Fintype V] [DecidableEq V] in
theorem internalImage_subset (ends : E → Sym2 V) (X : Finset V)
    (T : Finset (InternalEdge ends X)) : internalImage ends X T ⊆ edgesIn ends X := by
  intro e he
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
  exact a.property

omit [Fintype V] [DecidableEq V] in
theorem internalImage_card (ends : E → Sym2 V) (X : Finset V)
    (T : Finset (InternalEdge ends X)) : (internalImage ends X T).card = T.card :=
  Finset.card_image_of_injective _ Subtype.val_injective

omit [DecidableEq E] in
theorem parts_internal_disjoint (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) {X Y : Finset V}
    (hX : X ∈ P.parts) (hY : Y ∈ P.parts) (hne : X ≠ Y) :
    Disjoint (edgesIn ends X) (edgesIn ends Y) := by
  apply Finset.disjoint_left.mpr
  intro e heX heY
  have hex : ∃ u v, ends e = s(u, v) := by
    induction ends e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, rfl⟩
  obtain ⟨u, v, hev⟩ := hex
  have hu : u ∈ ends e := by simp [hev]
  exact Finset.disjoint_left.mp (P.disjoint hX hY hne)
    ((mem_edgesIn_iff ends X e).mp heX u hu)
    ((mem_edgesIn_iff ends Y e).mp heY u hu)

omit [DecidableEq E] in
theorem crossing_internal_disjoint (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) {X : Finset V} (hX : X ∈ P.parts) :
    Disjoint (crossing ends P) (edgesIn ends X) := by
  apply Finset.disjoint_left.mpr
  intro e he heX
  obtain ⟨u, v, hev, hn⟩ := Finset.mem_filter.mp he |>.2
  have hx := (mem_edgesIn_iff ends X e).mp heX
  exact hn ((P.part_eq_of_mem hX (hx u (by simp [hev]))).trans
    (P.part_eq_of_mem hX (hx v (by simp [hev]))).symm)

noncomputable def gluedEdges (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (T : ∀ X : PartitionVertex P, Finset (InternalEdge ends X.val))
    (Q : Finset (CrossingEdge ends P)) : Finset E :=
  Q.image Subtype.val ∪ Finset.univ.biUnion (fun X => internalImage ends X.val (T X))

theorem gluedEdges_card (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (T : ∀ X : PartitionVertex P, Finset (InternalEdge ends X.val))
    (Q : Finset (CrossingEdge ends P)) :
    (gluedEdges ends P T Q).card = Q.card + ∑ X, (T X).card := by
  have hdis : (Set.univ : Set (PartitionVertex P)).PairwiseDisjoint
      (fun X => internalImage ends X.val (T X)) := by
    intro X _ Y _ hXY
    exact (parts_internal_disjoint ends P X.property Y.property
      (fun h => hXY (Subtype.ext h))).mono
      (internalImage_subset ends X.val (T X)) (internalImage_subset ends Y.val (T Y))
  have hd : Disjoint (Q.image Subtype.val)
      (Finset.univ.biUnion (fun X => internalImage ends X.val (T X))) := by
    apply Finset.disjoint_left.mpr
    intro e he hE
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨X, _, hX⟩ := Finset.mem_biUnion.mp hE
    exact Finset.disjoint_left.mp (crossing_internal_disjoint ends P X.property)
      a.property (internalImage_subset ends X.val (T X) hX)
  rw [gluedEdges, Finset.card_union_of_disjoint hd,
    Finset.card_image_of_injective _ Subtype.val_injective, Finset.card_biUnion]
  · simp only [internalImage_card]
  · simpa only [Finset.coe_univ] using hdis

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh

theorem connected_of_fiber_paths {V Q : Type*} {G : SimpleGraph V} {H : SimpleGraph Q}
    (f : V → Q) (hs : Function.Surjective f) (hc : H.Connected)
    (hf : ∀ u v, f u = f v → G.Reachable u v)
    (he : ∀ A B, H.Adj A B → ∃ u v, f u = A ∧ f v = B ∧ G.Reachable u v) :
    G.Connected := by
  let g : Q → V := fun q => (hs q).choose
  have hg : ∀ q, f (g q) = q := fun q => (hs q).choose_spec
  have hmap : ∀ A B, H.Adj A B → G.Reachable (g A) (g B) := by
    intro A B hAB
    obtain ⟨u, v, hu, hv, huv⟩ := he A B hAB
    exact (hf (g A) u ((hg A).trans hu.symm)).trans
      (huv.trans (hf v (g B) (hv.trans (hg B).symm)))
  have : Nonempty Q := hc.nonempty
  have : Nonempty V := ⟨g (Classical.arbitrary Q)⟩
  constructor
  intro u v
  exact (hf u (g (f u)) (hg (f u)).symm).trans
    ((reachable_map_of_edges g hmap (hc (f u) (f v))).trans
      (hf (g (f v)) v (hg (f v))))

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical NagamochiIbaraki.EdgeConn
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [Fintype V] [DecidableEq V] in
theorem internalImage_reachable (ends : E → Sym2 V) (X : Finset V)
    (T : Finset (InternalEdge ends X)) {u v : X}
    (hr : (edgeGraph (restrictedEnds ends X) T).Reachable u v) :
    (edgeGraph ends (internalImage ends X T)).Reachable u.val v.val := by
  have h := reachable_vertex_map (restrictedEnds ends X) Subtype.val
    Subtype.val_injective T hr
  have hm : (fun e => Sym2.map Subtype.val (restrictedEnds ends X e)) =
      (fun e : InternalEdge ends X => ends e.val) := funext (restrictedEnds_map ends X)
  rw [hm] at h
  rw [internalImage, edgeGraph_image (fun e : InternalEdge ends X => ends e.val)
    ends Subtype.val (fun _ => rfl)]
  exact h

theorem gluedEdges_connected (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (T : ∀ X : PartitionVertex P, Finset (InternalEdge ends X.val))
    (Q : Finset (CrossingEdge ends P))
    (hT : ∀ X, IsSpanningTree (restrictedEnds ends X.val) (T X))
    (hQ : IsSpanningTree (quotientNativeEnds ends P) Q) :
    (edgeGraph ends (gluedEdges ends P T Q)).Connected := by
  apply connected_of_fiber_paths (partitionVertex P) (partitionVertex_surjective P)
    (spanningTree_simple _ hQ).connected
  · intro u v huv
    let X : PartitionVertex P := partitionVertex P u
    have hu : u ∈ X.val := P.mem_part_self.mpr (Finset.mem_univ u)
    have hv : v ∈ X.val := by
      have hh := congrArg Subtype.val huv
      exact hh ▸ P.mem_part_self.mpr (Finset.mem_univ v)
    have hr := (spanningTree_simple _ (hT X)).connected ⟨u, hu⟩ ⟨v, hv⟩
    apply (internalImage_reachable ends X.val (T X) hr).mono
    apply edgeGraph_mono
    intro e he
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨X, Finset.mem_univ X, he⟩)
  · intro A B hAB
    obtain ⟨⟨e, he, hev⟩, hne⟩ := (edgeGraph_adj_iff _ Q A B).mp hAB
    have hex : ∃ u v, ends e.val = s(u, v) := by
      induction ends e.val using Sym2.inductionOn with
      | _ u v => exact ⟨u, v, rfl⟩
    obtain ⟨u, v, huv⟩ := hex
    have hrep : s(partitionVertex P u, partitionVertex P v) = s(A, B) := by
      simpa only [quotientNativeEnds, quotientEnds, huv, Sym2.map_mk] using hev
    have heG : e.val ∈ gluedEdges ends P T Q :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    have huvne : u ≠ v := by
      intro h
      subst v
      have hdiag : (quotientNativeEnds ends P e).IsDiag := by
        simp [quotientNativeEnds, quotientEnds, huv]
      have hABeq : A = B := by simpa [hev] using hdiag
      exact hne hABeq
    have hr : (edgeGraph ends (gluedEdges ends P T Q)).Reachable u v :=
      ((edgeGraph_adj_iff _ _ _ _).mpr ⟨⟨e.val, heG, huv⟩, huvne⟩).reachable
    have hh : (partitionVertex P u = A ∧ partitionVertex P v = B) ∨
        (partitionVertex P u = B ∧ partitionVertex P v = A) := by simpa using hrep
    rcases hh with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact ⟨u, v, hu, hv, hr⟩
    · exact ⟨v, u, hv, hu, hr.symm⟩

theorem gluedEdges_tree (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (T : ∀ X : PartitionVertex P, Finset (InternalEdge ends X.val))
    (Q : Finset (CrossingEdge ends P))
    (hT : ∀ X, IsSpanningTree (restrictedEnds ends X.val) (T X))
    (hQ : IsSpanningTree (quotientNativeEnds ends P) Q) :
    IsSpanningTree ends (gluedEdges ends P T Q) := by
  have hc := gluedEdges_connected ends P T Q hT hQ
  have : Nonempty V := hc.nonempty
  apply tree_of_connected_card ends _ hc
  rw [gluedEdges_card]
  have hq := spanningTree_card _ hQ
  simp only [Fintype.card_coe] at hq
  have hi : ∀ X : PartitionVertex P, (T X).card + 1 = X.val.card := by
    intro X
    simpa only [Fintype.card_coe] using spanningTree_card _ (hT X)
  have hs := congrArg (fun f : PartitionVertex P → ℕ => ∑ X, f X) (funext hi)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_coe, smul_eq_mul, mul_one] at hs
  have hsum : (∑ X : PartitionVertex P, X.val.card) = Fintype.card V := by
    rw [Finset.sum_coe_sort]
    simpa only [Finset.card_univ] using P.sum_card_parts
  omega

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem gluedEdges_disjoint (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (T U : ∀ X : PartitionVertex P, Finset (InternalEdge ends X.val))
    (Q R : Finset (CrossingEdge ends P)) (hQ : Disjoint Q R)
    (hT : ∀ X, Disjoint (T X) (U X)) :
    Disjoint (gluedEdges ends P T Q) (gluedEdges ends P U R) := by
  have hc (A : Finset (CrossingEdge ends P)) : A.image Subtype.val ⊆ crossing ends P := by
    intro e he
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp he
    exact a.property
  apply Finset.disjoint_left.mpr
  intro e he hf
  rcases Finset.mem_union.mp he with he | he <;>
    rcases Finset.mem_union.mp hf with hf | hf
  · exact Finset.disjoint_left.mp ((Finset.disjoint_image Subtype.val_injective).mpr hQ) he hf
  · obtain ⟨X, _, hX⟩ := Finset.mem_biUnion.mp hf
    exact Finset.disjoint_left.mp (crossing_internal_disjoint ends P X.property)
      (hc Q he) (internalImage_subset ends X.val (U X) hX)
  · obtain ⟨X, _, hX⟩ := Finset.mem_biUnion.mp he
    exact Finset.disjoint_left.mp (crossing_internal_disjoint ends P X.property)
      (hc R hf) (internalImage_subset ends X.val (T X) hX)
  · obtain ⟨X, _, hX⟩ := Finset.mem_biUnion.mp he
    obtain ⟨Y, _, hY⟩ := Finset.mem_biUnion.mp hf
    by_cases hXY : X = Y
    · subst Y
      exact Finset.disjoint_left.mp ((Finset.disjoint_image Subtype.val_injective).mpr (hT X)) hX hY
    · exact Finset.disjoint_left.mp (parts_internal_disjoint ends P X.property Y.property
        (fun h => hXY (Subtype.ext h)))
        (internalImage_subset ends X.val (T X) hX) (internalImage_subset ends Y.val (U Y) hY)

theorem packing_glue (k : ℕ) (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V))
    (hT : ∀ X : PartitionVertex P, HasKTrees k (restrictedEnds ends X.val))
    (hQ : HasKTrees k (quotientNativeEnds ends P)) : HasKTrees k ends := by
  choose T hd ht using hT
  obtain ⟨Q, hqd, hqt⟩ := hQ
  refine ⟨fun i => gluedEdges ends P (fun X => T X i) (Q i), ?_, ?_⟩
  · intro i j hij
    exact gluedEdges_disjoint ends P _ _ _ _ (hqd i j hij) (fun X => hd X i j hij)
  · intro i
    exact gluedEdges_tree ends P _ _ (fun X => ht X i) (hqt i)

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem liftInternalSet_injective (X : Finset V) : Function.Injective (liftInternalSet X) := by
  intro A B h
  exact Finset.map_injective _ h

omit [DecidableEq V] in
theorem liftInternalSet_disjoint (X : Finset V) {A B : Finset X} (h : Disjoint A B) :
    Disjoint (liftInternalSet X A) (liftInternalSet X B) := by
  exact (Finset.disjoint_map _).mpr h

noncomputable def liftPartition (X : Finset V) (R : Finpartition (Finset.univ : Finset X)) :
    Finpartition X where
  parts := R.parts.image (liftInternalSet X)
  supIndep := by
    apply Finset.supIndep_iff_pairwiseDisjoint.mpr
    intro A hA B hB hAB
    obtain ⟨a, ha, haeq⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, hbeq⟩ := Finset.mem_image.mp hB
    subst A
    subst B
    exact liftInternalSet_disjoint X (R.disjoint ha hb (fun h => hAB (congrArg _ h)))
  sup_parts := by
    ext v
    simp only [Finset.mem_sup, Finset.mem_image, exists_exists_and_eq_and, id_eq]
    constructor
    · rintro ⟨A, _, hv⟩
      obtain ⟨a, _, rfl⟩ := Finset.mem_map.mp hv
      exact a.property
    · intro hv
      let a : X := ⟨v, hv⟩
      exact ⟨R.part a, R.part_mem.mpr (Finset.mem_univ a),
        Finset.mem_map.mpr ⟨a, R.mem_part_self.mpr (Finset.mem_univ a), rfl⟩⟩
  bot_notMem := by
    intro hh
    obtain ⟨A, hA, hA0⟩ := Finset.mem_image.mp hh
    have hne := R.nonempty_of_mem_parts hA
    obtain ⟨a, ha⟩ := hne
    have hm : a.val ∈ liftInternalSet X A := Finset.mem_map.mpr ⟨a, ha, rfl⟩
    rw [hA0] at hm
    exact Finset.notMem_empty _ hm

theorem liftPartition_card (X : Finset V) (R : Finpartition (Finset.univ : Finset X)) :
    (liftPartition X R).parts.card = R.parts.card := by
  exact Finset.card_image_of_injective _ (liftInternalSet_injective X)

theorem liftPartition_internal {E : Type*} [Fintype E] (ends : E → Sym2 V)
    (X : Finset V) (R : Finpartition (Finset.univ : Finset X)) :
    (∑ Y ∈ (liftPartition X R).parts, (edgesIn ends Y).card) =
      ∑ Y ∈ R.parts, (edgesIn (restrictedEnds ends X) Y).card := by
  change (∑ Y ∈ R.parts.image (liftInternalSet X), _) = _
  rw [Finset.sum_image (fun _ _ _ _ h => liftInternalSet_injective X h)]
  exact Finset.sum_congr rfl (fun Y _ => (internal_edges_card ends X Y).symm)

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V : Type*} [DecidableEq V] {S : Finset V}

noncomputable def refinePart (P : Finpartition S) (X : Finset V)
    (R : Finpartition X) : Finpartition S :=
  P.bind (fun Y _ => if h : Y = X then h.symm ▸ R else ⊤)

theorem top_parts_of_nonempty (X : Finset V) (hX : X.Nonempty) :
    (⊤ : Finpartition X).parts = {X} := by
  apply Finset.Subset.antisymm (Finpartition.parts_top_subset X)
  intro Y hY
  have : Y = X := Finset.mem_singleton.mp hY
  subst Y
  obtain ⟨A, hA⟩ := (⊤ : Finpartition X).parts_nonempty hX.ne_empty
  have hAX : A = X := Finset.mem_singleton.mp (Finpartition.parts_top_subset X hA)
  exact hAX ▸ hA

theorem refinePart_parts (P : Finpartition S) (X : Finset V) (hX : X ∈ P.parts)
    (R : Finpartition X) : (refinePart P X R).parts = (P.parts.erase X) ∪ R.parts := by
  ext Y
  rw [refinePart, Finpartition.mem_bind, Finset.mem_union]
  constructor
  · rintro ⟨A, hA, hY⟩
    by_cases hAX : A = X
    · subst A
      exact Or.inr (by simpa only [dite_true] using hY)
    · simp only [dif_neg hAX, top_parts_of_nonempty A (P.nonempty_of_mem_parts hA),
        Finset.mem_singleton] at hY
      subst Y
      exact Or.inl (Finset.mem_erase.mpr ⟨hAX, hA⟩)
  · rintro (hY | hY)
    · obtain ⟨hYX, hY⟩ := Finset.mem_erase.mp hY
      refine ⟨Y, hY, ?_⟩
      simp only [dif_neg hYX, top_parts_of_nonempty Y (P.nonempty_of_mem_parts hY),
        Finset.mem_singleton]
    · exact ⟨X, hX, by simpa only [dite_true] using hY⟩

theorem refinePart_disjoint (P : Finpartition S) (X : Finset V) (hX : X ∈ P.parts)
    (R : Finpartition X) : Disjoint (P.parts.erase X) R.parts := by
  apply Finset.disjoint_left.mpr
  intro Y hY hYR
  obtain ⟨hYX, hY⟩ := Finset.mem_erase.mp hY
  have hd := P.disjoint hY hX hYX
  have hz : Y = ∅ := by simpa using (hd.mono_right (R.le hYR)).eq_bot
  exact R.ne_empty hYR hz

theorem refinePart_card (P : Finpartition S) (X : Finset V) (hX : X ∈ P.parts)
    (R : Finpartition X) : (refinePart P X R).parts.card + 1 = P.parts.card + R.parts.card := by
  rw [refinePart_parts P X hX R, Finset.card_union_of_disjoint (refinePart_disjoint P X hX R)]
  have hc := Finset.card_erase_add_one hX
  omega

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

theorem refinePart_internal (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (X : Finset V) (hX : X ∈ P.parts)
    (R : Finpartition X) :
    (∑ Y ∈ (refinePart P X R).parts, (edgesIn ends Y).card) + (edgesIn ends X).card =
      (∑ Y ∈ P.parts, (edgesIn ends Y).card) + ∑ Y ∈ R.parts, (edgesIn ends Y).card := by
  rw [refinePart_parts P X hX R, Finset.sum_union (refinePart_disjoint P X hX R)]
  have he := Finset.sum_erase_add P.parts (fun Y => (edgesIn ends Y).card) hX
  omega

theorem refinePart_crossing (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (X : Finset V) (hX : X ∈ P.parts)
    (R : Finpartition (Finset.univ : Finset X)) :
    (crossing ends (refinePart P X (liftPartition X R))).card =
      (crossing ends P).card + (crossing (restrictedEnds ends X) R).card := by
  have h1 := partition_edge_count ends P
  have h2 := partition_edge_count ends (refinePart P X (liftPartition X R))
  have h3 := partition_edge_count (restrictedEnds ends X) R
  have h4 := refinePart_internal ends P X hX (liftPartition X R)
  rw [liftPartition_internal] at h4
  rw [Fintype.card_coe] at h3
  omega

theorem restriction_admissible (k : ℕ) (ends : E → Sym2 V)
    (ha : IsAdmissible k ends) (P : Finpartition (Finset.univ : Finset V))
    (hp : IsCriticalPartition k ends P) (X : Finset V) (hX : X ∈ P.parts) :
    IsAdmissible k (restrictedEnds ends X) := by
  intro R
  have h := ha (refinePart P X (liftPartition X R))
  have hc := refinePart_card P X hX (liftPartition X R)
  rw [liftPartition_card] at hc
  have hc' : ((refinePart P X (liftPartition X R)).parts.card : ℤ) + 1 =
      (P.parts.card : ℤ) + R.parts.card := by exact_mod_cast hc
  change (k : ℤ) * (((refinePart P X (liftPartition X R)).parts.card : ℤ) - 1) ≤ _ at h
  rw [refinePart_crossing ends P X hX R, Nat.cast_add] at h
  change ((crossing ends P).card : ℤ) = (k : ℤ) * ((P.parts.card : ℤ) - 1) at hp
  change (k : ℤ) * ((R.parts.card : ℤ) - 1) ≤ ((crossing (restrictedEnds ends X) R).card : ℤ)
  nlinarith

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem part_card_lt (P : Finpartition (Finset.univ : Finset V))
    (hp : 1 < P.parts.card) (X : PartitionVertex P) : X.val.card < Fintype.card V := by
  obtain ⟨Y, hY, hYX⟩ := Finset.exists_mem_ne hp X.val
  obtain ⟨v, hv⟩ := P.nonempty_of_mem_parts hY
  have hvn : v ∉ X.val := by
    exact fun hx => Finset.disjoint_left.mp (P.disjoint hY X.property hYX) hv hx
  have hss : X.val ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    exact hvn (heq.symm ▸ Finset.mem_univ v)
  simpa only [Finset.card_univ] using Finset.card_lt_card hss

omit [DecidableEq E] in
theorem restriction_size_lt (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (hp : 1 < P.parts.card)
    (X : PartitionVertex P) :
    Fintype.card X.val + Fintype.card (InternalEdge ends X.val) <
      Fintype.card V + Fintype.card E := by
  have hv := part_card_lt P hp X
  have he := Finset.card_le_univ (edgesIn ends X.val)
  simp only [Fintype.card_coe]
  omega

omit [DecidableEq E] in
theorem quotient_size_lt (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) (hp : P.parts.card < Fintype.card V) :
    Fintype.card (PartitionVertex P) + Fintype.card (CrossingEdge ends P) <
      Fintype.card V + Fintype.card E := by
  have he := Finset.card_le_univ (crossing ends P)
  simp only [Fintype.card_coe]
  omega

omit [DecidableEq E] in
theorem quotientNativeEnds_loopless (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) :
    ∀ e, ¬ (quotientNativeEnds ends P e).IsDiag := by
  intro e hh
  have hex : ∃ u v, ends e.val = s(u, v) := by
    induction ends e.val using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, rfl⟩
  obtain ⟨u, v, huv⟩ := hex
  have hne := (crossing_mk_iff ends P huv).mp e.property
  have heq : partitionVertex P u = partitionVertex P v := by
    simpa only [quotientNativeEnds, quotientEnds, huv, Sym2.map_mk, Sym2.mk_isDiag_iff] using hh
  exact hne (congrArg Subtype.val heq)

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]
    [DecidableEq E] [DecidableEq F]

theorem spanningTree_label_image (ends : E → Sym2 V) (ends' : F → Sym2 V)
    (f : E → F) (hi : Function.Injective f) (he : ∀ e, ends' (f e) = ends e)
    {T : Finset E} (ht : IsSpanningTree ends T) : IsSpanningTree ends' (T.image f) := by
  obtain ⟨_, hn, _, hf, hc⟩ := ht
  refine ⟨Finset.subset_univ _, hn, ?_, forest_image ends ends' f hi he hf, ?_⟩
  · exact fun _ _ v _ => Finset.mem_univ v
  · intro u hu v hv
    rw [edgeGraph_image ends ends' f he]
    exact hc u hu v hv

theorem hasKTrees_label_image (k : ℕ) (ends : E → Sym2 V) (ends' : F → Sym2 V)
    (f : E → F) (hi : Function.Injective f) (he : ∀ e, ends' (f e) = ends e)
    (ht : HasKTrees k ends) : HasKTrees k ends' := by
  obtain ⟨T, hd, ht⟩ := ht
  refine ⟨fun i => (T i).image f, ?_, ?_⟩
  · intro i j hij
    exact (Finset.disjoint_image hi).mpr (hd i j hij)
  · exact fun i => spanningTree_label_image ends ends' f hi he (ht i)

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev DeletedEdge (e : E) := {f : E // f ≠ e}

theorem deleted_crossing_image (ends : E → Sym2 V) (e : E)
    (P : Finpartition (Finset.univ : Finset V)) :
    (crossing (fun f : DeletedEdge e => ends f.val) P).image Subtype.val =
      (crossing ends P).erase e := by
  ext f
  simp only [Finset.mem_image, Finset.mem_erase]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨a.property, ?_⟩
    simpa only [crossing, Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · rintro ⟨hfe, hf⟩
    refine ⟨⟨f, hfe⟩, ?_, rfl⟩
    simpa only [crossing, Finset.mem_filter, Finset.mem_univ, true_and] using hf

theorem deleted_crossing_count (ends : E → Sym2 V) (e : E)
    (P : Finpartition (Finset.univ : Finset V)) :
    (crossing ends P).card ≤ (crossing (fun f : DeletedEdge e => ends f.val) P).card + 1 := by
  have hc : (crossing (fun f : DeletedEdge e => ends f.val) P).card =
      ((crossing ends P).erase e).card := by
    rw [← deleted_crossing_image ends e P, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [hc]
  by_cases he : e ∈ crossing ends P
  · exact (Finset.card_erase_add_one he).symm.le
  · rw [Finset.erase_eq_of_notMem he]
    omega

theorem delete_slack_admissible (k : ℕ) (ends : E → Sym2 V)
    (hs : ∀ P : Finpartition (Finset.univ : Finset V), 1 < P.parts.card →
      (k : ℤ) * ((P.parts.card : ℤ) - 1) < ((crossing ends P).card : ℤ)) (e : E) :
    IsAdmissible k (fun f : DeletedEdge e => ends f.val) := by
  intro P
  change (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ _
  by_cases hP : 1 < P.parts.card
  · have h := hs P hP
    have hc := deleted_crossing_count ends e P
    omega
  · have hle : (P.parts.card : ℤ) - 1 ≤ 0 := by omega
    exact le_trans (mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg k) hle) (by positivity)

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical NagamochiIbaraki.EdgeConn
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
theorem maximal_partition_crossing (ends : E → Sym2 V) (hl : ∀ e, ¬ (ends e).IsDiag)
    (P : Finpartition (Finset.univ : Finset V)) (hc : P.parts.card = Fintype.card V) :
    crossing ends P = Finset.univ := by
  have hinj : Function.Injective (partitionVertex P) := by
    apply (Fintype.bijective_iff_surjective_and_card _).mpr
      ⟨partitionVertex_surjective P, ?_⟩ |>.1
    simpa only [Fintype.card_coe] using hc.symm
  apply Finset.eq_univ_of_forall
  intro e
  have hex : ∃ u v, ends e = s(u, v) := by
    induction ends e using Sym2.inductionOn with
    | _ u v => exact ⟨u, v, rfl⟩
  obtain ⟨u, v, huv⟩ := hex
  apply (crossing_mk_iff ends P huv).mpr
  intro heq
  have he : u = v := hinj (Subtype.ext heq)
  exact hl e (by simp [huv, he])

omit [DecidableEq E] in
theorem admissible_total (k : ℕ) (ends : E → Sym2 V) (ha : IsAdmissible k ends) :
    (k : ℤ) * ((Fintype.card V : ℤ) - 1) ≤ Fintype.card E := by
  have h := ha (⊥ : Finpartition (Finset.univ : Finset V))
  have hc := Finset.card_le_univ (crossing ends (⊥ : Finpartition (Finset.univ : Finset V)))
  change (k : ℤ) * (((⊥ : Finpartition (Finset.univ : Finset V)).parts.card : ℤ) - 1) ≤ _ at h
  rw [Finpartition.card_bot, Finset.card_univ] at h
  exact h.trans (by exact_mod_cast hc)

omit [DecidableEq E] in
theorem no_tight_partition_slack (k : ℕ) (ends : E → Sym2 V)
    (hl : ∀ e, ¬ (ends e).IsDiag) (ha : IsAdmissible k ends)
    (hnc : ¬ IsCritical k ends)
    (hnp : ∀ P : Finpartition (Finset.univ : Finset V), IsCriticalPartition k ends P →
      ¬ (1 < P.parts.card ∧ P.parts.card < Fintype.card V)) :
    ∀ P : Finpartition (Finset.univ : Finset V), 1 < P.parts.card →
      (k : ℤ) * ((P.parts.card : ℤ) - 1) < ((crossing ends P).card : ℤ) := by
  intro P hP
  have hle := ha P
  change (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ ((crossing ends P).card : ℤ) at hle
  apply lt_of_le_of_ne hle
  intro heq
  have hp : IsCriticalPartition k ends P := heq.symm
  have hcard := P.card_parts_le_card
  simp only [Finset.card_univ] at hcard
  have hEq : P.parts.card = Fintype.card V := by
    have h := hnp P hp
    omega
  apply hnc
  change (Fintype.card E : ℤ) = (k : ℤ) * ((Fintype.card V : ℤ) - 1)
  rw [maximal_partition_crossing ends hl P hEq, Finset.card_univ, hEq] at heq
  exact heq.symm

omit [DecidableEq V] in
theorem singleton_packing [Nonempty V] (k : ℕ) (ends : E → Sym2 V)
    (hc : Fintype.card V = 1) : HasKTrees k ends := by
  have : Subsingleton V := ⟨Fintype.card_le_one_iff.mp hc.le⟩
  refine ⟨fun _ => ∅, ?_, ?_⟩
  · exact fun _ _ _ => Finset.disjoint_empty_left _
  · intro i
    refine ⟨Finset.empty_subset _, Finset.univ_nonempty, ?_, forest_empty ends, ?_⟩
    · exact fun _ _ v _ => Finset.mem_univ v
    · intro u _ v _
      have : u = v := Subsingleton.elim u v
      subst v
      exact SimpleGraph.Reachable.rfl

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

noncomputable def incidentDegree (ends : E → Sym2 V) (v : V) : ℕ :=
  Fintype.card {e : E // v ∈ ends e}

omit [Fintype V] in
theorem incidentDegree_eq_sum (ends : E → Sym2 V) (v : V) :
    incidentDegree ends v = ∑ e, if v ∈ ends e then 1 else 0 := by
  classical
  simp only [incidentDegree, Fintype.card_subtype, Finset.card_filter]

omit [Fintype V] in
theorem incidentDegree_eq_native (ends : E → Sym2 V) (v : V) :
    incidentDegree ends v = NagamochiIbaraki.EdgeConn.degIn ends Finset.univ v := by
  classical
  simp [incidentDegree, Fintype.card_subtype, NagamochiIbaraki.EdgeConn.degIn]

theorem degree_sum (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) :
    (∑ v, incidentDegree ends v) = 2 * Fintype.card E := by
  classical
  simp only [incidentDegree_eq_sum]
  rw [Finset.sum_comm]
  have hcount : ∀ e : E, (∑ v : V, if v ∈ ends e then 1 else 0) = 2 := by
    intro e
    have he : (Finset.univ.filter fun v => v ∈ ends e) = (ends e).toFinset := by
      ext v
      simp
    rw [← Finset.card_filter, he]
    exact Sym2.card_toFinset_of_not_isDiag (ends e) (hloop e)
  simp only [hcount, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  omega

theorem critical_low_degree (k : ℕ) (hk : 0 < k) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (hcritical : IsCritical k ends) :
    ∃ v, incidentDegree ends v < 2 * k := by
  classical
  by_contra! hn
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hn v)
  have hs := degree_sum ends hloop
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [hs] at hsum
  have hi : (Fintype.card V : ℤ) * (2 * k) ≤ 2 * (Fintype.card E : ℤ) := by exact_mod_cast hsum
  unfold IsCritical at hcritical
  have hki : 0 < (k : ℤ) := by exact_mod_cast hk
  nlinarith

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [DecidableEq V] [Fintype E]

abbrev DeletedVertex (v : V) := {w : V // w ≠ v}
abbrev RemainingEdge (ends : E → Sym2 V) (v : V) := {e : E // v ∉ ends e}

def deletedEnds (ends : E → Sym2 V) (v : V) : RemainingEdge ends v → Sym2 (DeletedVertex v) :=
  fun e => (ends e.val).pmap Subtype.mk (fun w hw hwe => e.property (hwe ▸ hw))

omit [DecidableEq V] [Fintype E] in
theorem deletedEnds_map (ends : E → Sym2 V) (v : V) (e : RemainingEdge ends v) :
    (deletedEnds ends v e).map Subtype.val = ends e.val := by
  exact Sym2.pmap_subtype_map_subtypeVal _ _

omit [DecidableEq V] [Fintype E] in
theorem deletedEnds_mem (ends : E → Sym2 V) (v : V) (e : RemainingEdge ends v)
    (w : DeletedVertex v) : w ∈ deletedEnds ends v e ↔ w.val ∈ ends e.val := by
  rw [← deletedEnds_map ends v e, Sym2.mem_map]
  constructor
  · intro hw
    exact ⟨w, hw, rfl⟩
  · rintro ⟨z, hz, he⟩
    have : z = w := Subtype.ext he
    exact this ▸ hz

omit [DecidableEq V] [Fintype E] in
theorem deletedEnds_loopless (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) :
    ∀ e, ¬ (deletedEnds ends v e).IsDiag := by
  intro e he
  have hm : ((deletedEnds ends v e).map Subtype.val).IsDiag := Sym2.IsDiag.map (f := Subtype.val) he
  rw [deletedEnds_map] at hm
  exact hloop e.val hm

def deletedVertexEmbedding (v : V) : DeletedVertex v ↪ V := ⟨Subtype.val, Subtype.val_injective⟩

def liftDeletedSet (v : V) (X : Finset (DeletedVertex v)) : Finset V :=
  X.map (deletedVertexEmbedding v)

omit [DecidableEq V] in
theorem center_not_liftDeletedSet (v : V) (X : Finset (DeletedVertex v)) :
    v ∉ liftDeletedSet v X := by
  intro hv
  obtain ⟨w, _, hw⟩ := Finset.mem_map.mp hv
  exact w.property hw

omit [DecidableEq V] in
theorem mem_liftDeletedSet (v : V) (X : Finset (DeletedVertex v)) (w : DeletedVertex v) :
    w.val ∈ liftDeletedSet v X ↔ w ∈ X := by
  simp [liftDeletedSet, deletedVertexEmbedding]

noncomputable def deletedCapacity (ends : E → Sym2 V) (v : V) (w : DeletedVertex v) : ℤ :=
  Fintype.card {e : E // ends e = s(v, w.val)}

theorem deletedCapacity_nonneg (ends : E → Sym2 V) (v : V) (w : DeletedVertex v) :
    0 ≤ deletedCapacity ends v w := by
  unfold deletedCapacity
  positivity

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

abbrev IncidentEdge (ends : E → Sym2 V) (v : V) := {e : E // v ∈ ends e}

noncomputable def otherEndpoint (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (e : IncidentEdge ends v) : DeletedVertex v :=
  ⟨Sym2.Mem.other e.property, Sym2.other_ne (hloop e.val) e.property⟩

omit [Fintype V] [DecidableEq V] [Fintype E] in
theorem otherEndpoint_spec (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (e : IncidentEdge ends v) :
    s(v, (otherEndpoint ends hloop v e).val) = ends e.val :=
  Sym2.other_spec e.property

omit [Fintype V] [DecidableEq V] in
theorem pair_right_injective (v : V) : Function.Injective (fun w : V => s(v, w)) := by
  intro w z h
  have hh : (v = v ∧ w = z) ∨ (v = z ∧ w = v) := by simpa using h
  rcases hh with ⟨_, hw⟩ | ⟨hz, hw⟩
  · exact hw
  · exact hw.trans hz


noncomputable def incidentFiberEquiv (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (w : DeletedVertex v) :
    {e : E // ends e = s(v, w.val)} ≃
      {e : IncidentEdge ends v // otherEndpoint ends hloop v e = w} where
  toFun e := ⟨⟨e.val, by rw [e.property]; exact Sym2.mem_mk_left _ _⟩, by
    apply Subtype.ext
    apply pair_right_injective v
    exact (otherEndpoint_spec ends hloop v _).trans e.property⟩
  invFun e := ⟨e.val.val, by rw [← otherEndpoint_spec ends hloop v e.val, e.property]⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
theorem deletedCapacity_fiber (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (w : DeletedVertex v) :
    deletedCapacity ends v w =
      (Fintype.card {e : IncidentEdge ends v // otherEndpoint ends hloop v e = w} : ℤ) := by
  unfold deletedCapacity
  exact_mod_cast Fintype.card_congr (incidentFiberEquiv ends hloop v w)

theorem sum_fiber_card {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (f : A → B) (X : Finset B) :
    (∑ b ∈ X, (Fintype.card {a : A // f a = b} : ℤ)) =
      (Fintype.card {a : A // f a ∈ X} : ℤ) := by
  classical
  simp only [Fintype.card_subtype, Finset.card_filter, Nat.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

theorem deletedCapacity_sum (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (X : Finset (DeletedVertex v)) :
    (∑ w ∈ X, deletedCapacity ends v w) =
      (Fintype.card {e : IncidentEdge ends v // otherEndpoint ends hloop v e ∈ X} : ℤ) := by
  simp_rw [deletedCapacity_fiber ends hloop v]
  exact sum_fiber_card _ _

theorem deletedCapacity_total (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) :
    (∑ w, deletedCapacity ends v w) = (incidentDegree ends v : ℤ) := by
  rw [deletedCapacity_sum ends hloop v]
  simp [incidentDegree]

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical

namespace NashWilliams61.TreePacking.NWFresh

variable {V E J : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype J]

abbrev EndpointOccurrence (v : V) (a : J → Sym2 (DeletedVertex v)) :=
  Σ w : DeletedVertex v, {j : J // w ∈ a j}

noncomputable def oldSelected (ends : E → Sym2 V) (v : V)
    (T : Finset (RemainingEdge ends v ⊕ J)) : Finset (RemainingEdge ends v) :=
  Finset.univ.filter fun e => Sum.inl e ∈ T

noncomputable def newSelected (ends : E → Sym2 V) (v : V)
    (T : Finset (RemainingEdge ends v ⊕ J)) : Finset J :=
  Finset.univ.filter fun j => Sum.inr j ∈ T

noncomputable def oldLift (ends : E → Sym2 V) (v : V)
    (T : Finset (RemainingEdge ends v ⊕ J)) : Finset E :=
  (oldSelected ends v T).image Subtype.val

noncomputable def selectedOccurrences (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (T : Finset (RemainingEdge ends v ⊕ J)) :
    Finset (EndpointOccurrence v a) := Finset.univ.filter fun p => Sum.inr p.2.val ∈ T

noncomputable def newLift (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (T : Finset (RemainingEdge ends v ⊕ J)) : Finset E :=
  (selectedOccurrences ends v a T).image (fun p => (f p).val)

noncomputable def expandedEdges (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (T : Finset (RemainingEdge ends v ⊕ J)) : Finset E :=
  oldLift ends v T ∪ newLift ends v a f T

omit [Fintype V] in
theorem selected_card (ends : E → Sym2 V) (v : V)
    (T : Finset (RemainingEdge ends v ⊕ J)) :
    (oldSelected ends v T).card + (newSelected ends v T).card = T.card := by
  classical
  have he : (oldSelected ends v T).disjSum (newSelected ends v T) = T := by
    ext e
    cases e <;> simp [oldSelected, newSelected]
  rw [← Finset.card_disjSum, he]

omit [Fintype V] [Fintype J] in
theorem oldLift_card (ends : E → Sym2 V) (v : V)
    (T : Finset (RemainingEdge ends v ⊕ J)) :
    (oldLift ends v T).card = (oldSelected ends v T).card := by
  exact Finset.card_image_of_injective _ Subtype.val_injective

omit [Fintype V] [Fintype J] in
theorem oldLift_not_incident (ends : E → Sym2 V) (v : V)
    (T : Finset (RemainingEdge ends v ⊕ J)) {e : E} (he : e ∈ oldLift ends v T) :
    v ∉ ends e := by
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp he
  exact e.property

omit [Fintype E] in
theorem newLift_incident (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (T : Finset (RemainingEdge ends v ⊕ J)) {e : E} (he : e ∈ newLift ends v a f T) :
    v ∈ ends e := by
  obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
  exact (f p).property

theorem old_new_disjoint (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (T U : Finset (RemainingEdge ends v ⊕ J)) :
    Disjoint (oldLift ends v T) (newLift ends v a f U) := by
  apply Finset.disjoint_left.mpr
  intro e he hne
  exact oldLift_not_incident ends v T he (newLift_incident ends v a f U hne)

theorem expanded_disjoint (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (hf : Function.Injective f) {T U : Finset (RemainingEdge ends v ⊕ J)}
    (hTU : Disjoint T U) : Disjoint (expandedEdges ends v a f T) (expandedEdges ends v a f U) := by
  classical
  apply Finset.disjoint_left.mpr
  intro e heT heU
  rcases Finset.mem_union.mp heT with hoT | hnT <;>
    rcases Finset.mem_union.mp heU with hoU | hnU
  · obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hoT
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hoU
    have hxy : x = y := Subtype.ext (hxe.trans hye.symm)
    subst y
    exact Finset.disjoint_left.mp hTU ((Finset.mem_filter.mp hx).2) ((Finset.mem_filter.mp hy).2)
  · exact Finset.disjoint_left.mp (old_new_disjoint ends v a f T U) hoT hnU
  · exact Finset.disjoint_left.mp (old_new_disjoint ends v a f U T) hoU hnT
  · obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hnT
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp hnU
    have hpq : p = q := hf (Subtype.ext (hpe.trans hqe.symm))
    subst q
    exact Finset.disjoint_left.mp hTU ((Finset.mem_filter.mp hp).2) ((Finset.mem_filter.mp hq).2)

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical

namespace NashWilliams61.TreePacking.NWFresh

variable {V E J : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype J]

theorem expanded_old_mem (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (T : Finset (RemainingEdge ends v ⊕ J)) (e : RemainingEdge ends v)
    (he : Sum.inl e ∈ T) : e.val ∈ expandedEdges ends v a f T := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨e, by simp [oldSelected, he], rfl⟩

theorem expanded_new_mem (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (T : Finset (RemainingEdge ends v ⊕ J)) (p : EndpointOccurrence v a)
    (hp : Sum.inr p.2.val ∈ T) : (f p).val ∈ expandedEdges ends v a f T := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨p, by simp [selectedOccurrences, hp], rfl⟩

omit [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype J] in
theorem allocated_edge_endpoints (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (a : J → Sym2 (DeletedVertex v))
    (f : EndpointOccurrence v a → IncidentEdge ends v)
    (hf : ∀ p, otherEndpoint ends hloop v (f p) = p.1) (p : EndpointOccurrence v a) :
    ends (f p).val = s(v, p.1.val) := by
  rw [← otherEndpoint_spec ends hloop v (f p), hf p]

theorem expanded_center_reachable (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (a : J → Sym2 (DeletedVertex v))
    (f : EndpointOccurrence v a → IncidentEdge ends v)
    (hf : ∀ p, otherEndpoint ends hloop v (f p) = p.1)
    (T : Finset (RemainingEdge ends v ⊕ J)) (p : EndpointOccurrence v a)
    (hp : Sum.inr p.2.val ∈ T) :
    (edgeGraph ends (expandedEdges ends v a f T)).Reachable v p.1.val := by
  apply SimpleGraph.Adj.reachable
  apply (edgeGraph_adj_iff _ _ _ _).mpr
  exact ⟨⟨(f p).val, expanded_new_mem ends v a f T p hp,
    allocated_edge_endpoints ends hloop v a f hf p⟩, Ne.symm p.1.property⟩

theorem expanded_reachable (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (a : J → Sym2 (DeletedVertex v))
    (f : EndpointOccurrence v a → IncidentEdge ends v)
    (hf : ∀ p, otherEndpoint ends hloop v (f p) = p.1)
    (T : Finset (RemainingEdge ends v ⊕ J)) {x y : DeletedVertex v}
    (hxy : (edgeGraph (Sum.elim (deletedEnds ends v) a) T).Reachable x y) :
    (edgeGraph ends (expandedEdges ends v a f T)).Reachable x.val y.val := by
  apply reachable_map_of_edges Subtype.val _ hxy
  intro x y h
  obtain ⟨⟨e, he, hexy⟩, hne⟩ := (edgeGraph_adj_iff _ _ _ _).mp h
  cases e with
  | inl e =>
    apply SimpleGraph.Adj.reachable
    apply (edgeGraph_adj_iff _ _ _ _).mpr
    refine ⟨⟨e.val, expanded_old_mem ends v a f T e he, ?_⟩, ?_⟩
    · have hm := congrArg (Sym2.map (Subtype.val : DeletedVertex v → V)) hexy
      simpa only [Sum.elim_inl, deletedEnds_map, Sym2.map_mk] using hm
    · exact fun hh => hne (Subtype.ext hh)
  | inr j =>
    have hx : x ∈ a j := by rw [show a j = s(x,y) from hexy]; exact Sym2.mem_mk_left _ _
    have hy : y ∈ a j := by rw [show a j = s(x,y) from hexy]; exact Sym2.mem_mk_right _ _
    exact (expanded_center_reachable ends hloop v a f hf T ⟨x, ⟨j, hx⟩⟩ he).symm.trans
      (expanded_center_reachable ends hloop v a f hf T ⟨y, ⟨j, hy⟩⟩ he)

theorem expanded_connected (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (a : J → Sym2 (DeletedVertex v))
    (f : EndpointOccurrence v a → IncidentEdge ends v)
    (hf : ∀ p, otherEndpoint ends hloop v (f p) = p.1)
    (T : Finset (RemainingEdge ends v ⊕ J))
    (hT : IsSpanningTree (Sum.elim (deletedEnds ends v) a) T)
    (hnew : (newSelected ends v T).Nonempty) :
    (edgeGraph ends (expandedEdges ends v a f T)).Connected := by
  obtain ⟨j, hj⟩ := hnew
  have hjT : Sum.inr j ∈ T := (Finset.mem_filter.mp hj).2
  obtain ⟨x, y, haxy⟩ : ∃ x y, a j = s(x,y) := by
    induction a j using Sym2.inductionOn with
    | _ x y => exact ⟨x,y,rfl⟩
  have hx : x ∈ a j := by rw [haxy]; exact Sym2.mem_mk_left _ _
  have hroot := expanded_center_reachable ends hloop v a f hf T ⟨x, ⟨j,hx⟩⟩ hjT
  have hall : ∀ z : V, (edgeGraph ends (expandedEdges ends v a f T)).Reachable v z := by
    intro z
    by_cases hz : z = v
    · subst z
      exact SimpleGraph.Reachable.rfl
    · exact hroot.trans (expanded_reachable ends hloop v a f hf T
        (hT.2.2.2.2 x (Finset.mem_univ _) ⟨z,hz⟩ (Finset.mem_univ _)))
  let : Nonempty V := ⟨v⟩
  constructor
  intro x y
  exact (hall x).symm.trans (hall y)

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

omit [Fintype V] in
theorem remaining_internal_iff (ends : E → Sym2 V) (v : V)
    (X : Finset (DeletedVertex v)) (e : RemainingEdge ends v) :
    e ∈ edgesIn (deletedEnds ends v) X ↔ e.val ∈ edgesIn ends (liftDeletedSet v X) := by
  rw [mem_edgesIn_iff, mem_edgesIn_iff]
  constructor
  · intro h w hw
    have hn : w ≠ v := by intro he; exact e.property (he ▸ hw)
    exact (mem_liftDeletedSet v X ⟨w, hn⟩).mpr (h _ ((deletedEnds_mem ends v e _).mpr hw))
  · intro h w hw
    exact (mem_liftDeletedSet v X w).mp (h _ ((deletedEnds_mem ends v e w).mp hw))

omit [Fintype V] in
theorem remaining_insert_internal_iff (ends : E → Sym2 V) (v : V)
    (X : Finset (DeletedVertex v)) (e : RemainingEdge ends v) :
    e.val ∈ edgesIn ends (insert v (liftDeletedSet v X)) ↔
      e ∈ edgesIn (deletedEnds ends v) X := by
  rw [remaining_internal_iff, mem_edgesIn_iff, mem_edgesIn_iff]
  constructor
  · intro h w hw
    rcases Finset.mem_insert.mp (h w hw) with he | hin
    · exact False.elim (e.property (he ▸ hw))
    · exact hin
  · intro h w hw
    exact Finset.mem_insert_of_mem (h w hw)

omit [Fintype V] in
theorem incident_insert_internal_iff (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V)
    (X : Finset (DeletedVertex v)) (e : IncidentEdge ends v) :
    e.val ∈ edgesIn ends (insert v (liftDeletedSet v X)) ↔
      otherEndpoint ends hloop v e ∈ X := by
  rw [mem_edgesIn_iff]
  constructor
  · intro h
    have hm := h (otherEndpoint ends hloop v e).val (Sym2.other_mem e.property)
    rcases Finset.mem_insert.mp hm with he | hin
    · exact False.elim ((otherEndpoint ends hloop v e).property he)
    · exact (mem_liftDeletedSet v X _).mp hin
  · intro h w hw
    rw [← otherEndpoint_spec ends hloop v e, Sym2.mem_iff] at hw
    rcases hw with rfl | rfl
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem ((mem_liftDeletedSet v X _).mpr h)

noncomputable def deletionInternalEquiv (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (X : Finset (DeletedVertex v)) :
    {e : E // e ∈ edgesIn ends (insert v (liftDeletedSet v X))} ≃
      ({e : RemainingEdge ends v // e ∈ edgesIn (deletedEnds ends v) X} ⊕
        {e : IncidentEdge ends v // otherEndpoint ends hloop v e ∈ X}) where
  toFun e := if h : v ∈ ends e.val then
      Sum.inr ⟨⟨e.val, h⟩, (incident_insert_internal_iff ends hloop v X _).mp e.property⟩
    else Sum.inl ⟨⟨e.val, h⟩, (remaining_insert_internal_iff ends v X _).mp e.property⟩
  invFun e := match e with
    | Sum.inl e => ⟨e.val.val, (remaining_insert_internal_iff ends v X e.val).mpr e.property⟩
    | Sum.inr e => ⟨e.val.val, (incident_insert_internal_iff ends hloop v X e.val).mpr e.property⟩
  left_inv e := by
    dsimp
    split_ifs <;> rfl
  right_inv e := by
    cases e with
    | inl e => simp only [dif_neg e.val.property]
    | inr e => simp only [dif_pos e.val.property]

theorem internal_insert_count (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (X : Finset (DeletedVertex v)) :
    ((edgesIn ends (insert v (liftDeletedSet v X))).card : ℤ) =
      (edgesIn (deletedEnds ends v) X).card + ∑ w ∈ X, deletedCapacity ends v w := by
  classical
  have he := Fintype.card_congr (deletionInternalEquiv ends hloop v X)
  simp only [Fintype.card_sum, Fintype.card_coe] at he
  rw [deletedCapacity_sum ends hloop v X]
  exact_mod_cast he

noncomputable def remainingInternalEquiv (ends : E → Sym2 V) (v : V)
    (X : Finset (DeletedVertex v)) :
    {e : RemainingEdge ends v // e ∈ edgesIn (deletedEnds ends v) X} ≃
      {e : E // e ∈ edgesIn ends (liftDeletedSet v X)} where
  toFun e := ⟨e.val.val, (remaining_internal_iff ends v X e.val).mp e.property⟩
  invFun e := ⟨⟨e.val, by
    intro hv
    exact center_not_liftDeletedSet v X ((mem_edgesIn_iff ends _ _).mp e.property v hv)⟩,
    (remaining_internal_iff ends v X _).mpr e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype V] in
theorem internal_deleted_count (ends : E → Sym2 V) (v : V)
    (X : Finset (DeletedVertex v)) :
    (edgesIn (deletedEnds ends v) X).card = (edgesIn ends (liftDeletedSet v X)).card := by
  classical
  simpa only [Fintype.card_coe] using Fintype.card_congr (remainingInternalEquiv ends v X)

omit [Fintype V] in
theorem delta_deleted (k : ℕ) (ends : E → Sym2 V) (v : V)
    (X : Finset (DeletedVertex v)) :
    Delta k (deletedEnds ends v) X = Delta k ends (liftDeletedSet v X) := by
  simp only [Delta, internal_deleted_count, liftDeletedSet, Finset.card_map]

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem capacity_sum_mono (g : V → ℤ) (hg : ∀ v, 0 ≤ g v)
    {A B : Finset V} (hAB : A ⊆ B) :
    (∑ v ∈ A, g v) ≤ ∑ v ∈ B, g v :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun v _ _ => hg v)

omit [Fintype V] [DecidableEq V] in
theorem capacity_positive (g : V → ℤ) {A : Finset V}
    (hA : 0 < ∑ v ∈ A, g v) : ∃ v ∈ A, 0 < g v := by
  by_contra! h
  have hz := Finset.sum_nonpos h
  omega

omit [Fintype V] in
theorem capacity_sum_le_of_support (g : V → ℤ) (hg : ∀ v, 0 ≤ g v)
    {A B : Finset V} (hAB : ∀ v ∈ A, v ∉ B → g v = 0) :
    (∑ v ∈ A, g v) ≤ ∑ v ∈ B, g v := by
  have he : (∑ v ∈ A ∩ B, g v) = ∑ v ∈ A, g v := by
    apply Finset.sum_subset Finset.inter_subset_left
    intro v hv hvn
    exact hAB v hv (by intro hvB; exact hvn (Finset.mem_inter.mpr ⟨hv, hvB⟩))
  rw [← he]
  exact capacity_sum_mono g hg Finset.inter_subset_right

theorem crucial_sets_meet (D : Finset V → ℤ) (g : V → ℤ) (s : ℤ)
    (hg : ∀ v, 0 ≤ g v) (htotal : 2 * s < ∑ v, g v)
    (hD : ∀ X, X.Nonempty → 0 ≤ D X)
    {X Y : Finset V} (hX : X.Nonempty) (hY : Y.Nonempty)
    (hGX : deficiencyGamma D g s X = 0)
    (hGY : deficiencyGamma D g s Y = 0) : (X ∩ Y).Nonempty := by
  have hx := hD X hX
  have hy := hD Y hY
  have hm := outsideMass_modular g X Y
  have hu : 0 ≤ outsideMass g (X ∪ Y) := Finset.sum_nonneg (fun v _ => hg v)
  by_contra hn
  have he : X ∩ Y = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
  simp only [he, outsideMass, Finset.sdiff_empty] at hm
  unfold deficiencyGamma at hGX hGY
  change 0 ≤ outsideMass g (X ∪ Y) at hu
  change outsideMass g (X ∪ Y) + (∑ v, g v) =
    outsideMass g X + outsideMass g Y at hm
  omega

theorem select_positive_first (g : V → ℤ) (s : ℤ) (I : Finset V)
    (hg : ∀ v, 0 ≤ g v) (hs : 0 < s) (htotal : 2 * s < ∑ v, g v)
    (hI : outsideMass g I ≤ s) :
    ∃ v, 0 < g v ∧ (∑ w ∈ (Finset.univ \ I).erase v, g w) < s := by
  by_cases hstrict : outsideMass g I < s
  · obtain ⟨v, _, hv⟩ := capacity_positive g (A := Finset.univ) (by omega)
    refine ⟨v, hv, ?_⟩
    exact lt_of_le_of_lt (capacity_sum_mono g hg (Finset.erase_subset _ _)) hstrict
  · have heq : outsideMass g I = s := by omega
    obtain ⟨v, hvI, hv⟩ := capacity_positive g (A := Finset.univ \ I) (by change 0 < outsideMass g I; omega)
    refine ⟨v, hv, ?_⟩
    have he := Finset.sum_erase_add (Finset.univ \ I) g hvI
    change (∑ w ∈ (Finset.univ \ I).erase v, g w) + g v = outsideMass g I at he
    omega

theorem select_positive_second (g : V → ℤ) (s : ℤ) (I U : Finset V)
    (hg : ∀ v, 0 ≤ g v) (v : V) (hvU : v ∈ U)
    (hfirst : (∑ w ∈ (Finset.univ \ I).erase v, g w) < s)
    (hU : s ≤ outsideMass g U) :
    ∃ w, w ∈ I ∧ w ∉ U ∧ 0 < g w := by
  by_contra! hn
  have hle := capacity_sum_le_of_support g hg
    (A := Finset.univ \ U) (B := (Finset.univ \ I).erase v) (by
      intro w hw hwb
      have hwU := (Finset.mem_sdiff.mp hw).2
      have hwv : w ≠ v := by intro h; subst w; exact hwU hvU
      have hwI : w ∈ I := by
        by_contra hwi
        exact hwb (Finset.mem_erase.mpr ⟨hwv, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hwi⟩⟩)
      exact le_antisymm (hn w hwI hwU) (hg w))
  change outsideMass g U ≤ _ at hle
  omega

theorem augmentation_endpoints (D : Finset V → ℤ) (g : V → ℤ) (s : ℤ)
    (hsub : IntersectSubmodular D) (hD : ∀ X, X.Nonempty → 0 ≤ D X)
    (hsingle : ∀ v, D {v} = 0) (hg : ∀ v, 0 ≤ g v)
    (hs : 0 < s) (htotal : 2 * s < ∑ v, g v)
    (hGamma : ∀ X, X.Nonempty → 0 ≤ deficiencyGamma D g s X) :
    ∃ v w, v ≠ w ∧ 0 < g v ∧ 0 < g w ∧
      (∀ X, X.Nonempty → D X = 0 → ¬ (v ∈ X ∧ w ∈ X)) ∧
      (∀ X, X.Nonempty → deficiencyGamma D g s X = 0 → v ∈ X ∨ w ∈ X) := by
  classical
  have hI : ∃ I : Finset V, outsideMass g I ≤ s ∧
      ∀ X, X.Nonempty → deficiencyGamma D g s X = 0 → I ⊆ X := by
    by_cases hex : ∃ X, X.Nonempty ∧ deficiencyGamma D g s X = 0
    · obtain ⟨I, hi, hz, hmin⟩ := least_zero_set (gamma_submodular hsub g s)
        hGamma (fun X Y hX hY hGX hGY => crucial_sets_meet D g s hg htotal hD hX hY hGX hGY) hex
      refine ⟨I, ?_, hmin⟩
      have hd := hD I hi
      unfold deficiencyGamma at hz
      omega
    · refine ⟨Finset.univ, ?_, ?_⟩
      · simp [outsideMass]
        omega
      · intro X hX hGX
        exact False.elim (hex ⟨X, hX, hGX⟩)
  obtain ⟨I, hcapI, hcontain⟩ := hI
  obtain ⟨v, hgv, hfirst⟩ := select_positive_first g s I hg hs htotal hcapI
  obtain ⟨U, hvU, hDU, hmax⟩ := greatest_zero_containing hsub hD v (hsingle v)
  have hcapU : s ≤ outsideMass g U := by
    have h := hGamma U ⟨v, hvU⟩
    unfold deficiencyGamma at h
    omega
  obtain ⟨w, hwI, hwU, hgw⟩ := select_positive_second g s I U hg v hvU hfirst hcapU
  refine ⟨v, w, ?_, hgv, hgw, ?_, ?_⟩
  · intro he
    exact hwU (he ▸ hvU)
  · intro X _ hDX hvw
    exact hwU (hmax X hvw.1 hDX hvw.2)
  · intro X hX hGX
    exact Or.inr (hcontain X hX hGX hwI)

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V : Type*} [Fintype V] [DecidableEq V]

def consumePair (g : V → ℤ) (v w : V) (x : V) : ℤ :=
  g x - (if x = v then 1 else 0) - (if x = w then 1 else 0)

def addEdgeDeficiency (D : Finset V → ℤ) (v w : V) (X : Finset V) : ℤ :=
  D X - if v ∈ X ∧ w ∈ X then 1 else 0

omit [Fintype V] in
theorem consumePair_nonneg (g : V → ℤ) (hg : ∀ x, 0 ≤ g x)
    {v w : V} (hvw : v ≠ w) (hv : 0 < g v) (hw : 0 < g w) :
    ∀ x, 0 ≤ consumePair g v w x := by
  intro x
  unfold consumePair
  by_cases hxv : x = v
  · subst x
    simp only [if_neg hvw]
    omega
  · by_cases hxw : x = w
    · subst x
      simp only [if_neg hxv]
      omega
    · simp only [if_neg hxv, if_neg hxw, sub_zero]
      exact hg x

omit [Fintype V] in
theorem consumePair_sum (g : V → ℤ) (v w : V) (X : Finset V) :
    (∑ x ∈ X, consumePair g v w x) =
      (∑ x ∈ X, g x) - (if v ∈ X then 1 else 0) - (if w ∈ X then 1 else 0) := by
  simp [consumePair, Finset.sum_sub_distrib]

theorem consumePair_total (g : V → ℤ) (v w : V) :
    (∑ x, consumePair g v w x) = (∑ x, g x) - 2 := by
  rw [consumePair_sum]
  simp
  ring

theorem outsideMass_consumePair (g : V → ℤ) (v w : V) (X : Finset V) :
    outsideMass (consumePair g v w) X = outsideMass g X -
      (if v ∈ X then 0 else 1) - (if w ∈ X then 0 else 1) := by
  unfold outsideMass
  rw [consumePair_sum]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
  split_ifs <;> omega

omit [Fintype V] in
theorem addEdgeDeficiency_nonneg (D : Finset V → ℤ) (v w : V)
    (hD : ∀ X, X.Nonempty → 0 ≤ D X)
    (hcritical : ∀ X, X.Nonempty → D X = 0 → ¬ (v ∈ X ∧ w ∈ X)) :
    ∀ X, X.Nonempty → 0 ≤ addEdgeDeficiency D v w X := by
  intro X hX
  have h := hD X hX
  unfold addEdgeDeficiency
  split_ifs with hvw
  · have hn : D X ≠ 0 := by intro hz; exact hcritical X hX hz hvw
    omega
  · simpa only [sub_zero] using h

theorem gamma_after_augmentation (D : Finset V → ℤ) (g : V → ℤ)
    (s : ℤ) (v w : V) (X : Finset V) :
    deficiencyGamma (addEdgeDeficiency D v w) (consumePair g v w) (s - 1) X =
      deficiencyGamma D g s X - (if v ∉ X ∧ w ∉ X then 1 else 0) := by
  simp only [deficiencyGamma, addEdgeDeficiency, outsideMass_consumePair]
  by_cases hv : v ∈ X <;> by_cases hw : w ∈ X <;> simp [hv, hw] <;> ring

theorem gamma_augmentation_nonneg (D : Finset V → ℤ) (g : V → ℤ)
    (s : ℤ) (v w : V)
    (hG : ∀ X, X.Nonempty → 0 ≤ deficiencyGamma D g s X)
    (hcrucial : ∀ X, X.Nonempty → deficiencyGamma D g s X = 0 → v ∈ X ∨ w ∈ X) :
    ∀ X, X.Nonempty →
      0 ≤ deficiencyGamma (addEdgeDeficiency D v w) (consumePair g v w) (s - 1) X := by
  intro X hX
  rw [gamma_after_augmentation]
  have h := hG X hX
  split_ifs with hnone
  · have hn : deficiencyGamma D g s X ≠ 0 := by
      intro hz
      rcases hcrucial X hX hz with hv | hw
      · exact hnone.1 hv
      · exact hnone.2 hw
    omega
  · simpa only [sub_zero] using h

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

def appendEdge (ends : E → Sym2 V) (v w : V) : E ⊕ Unit → Sym2 V :=
  Sum.elim ends (fun _ => s(v, w))

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem appendEdge_loopless (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    {v w : V} (hvw : v ≠ w) : ∀ e, ¬ (appendEdge ends v w e).IsDiag := by
  intro e
  cases e with
  | inl e => exact hloop e
  | inr u => simpa [appendEdge, Sym2.mk_isDiag_iff] using hvw

omit [Fintype V] in
theorem edgesIn_appendEdge (ends : E → Sym2 V) (v w : V) (X : Finset V) :
    edgesIn (appendEdge ends v w) X = (edgesIn ends X).disjSum
      (if v ∈ X ∧ w ∈ X then (Finset.univ : Finset Unit) else ∅) := by
  classical
  ext e
  cases e with
  | inl e => simp [mem_edgesIn_iff, appendEdge]
  | inr u =>
    simp only [mem_edgesIn_iff, appendEdge, Sum.elim_inr]
    by_cases h : v ∈ X ∧ w ∈ X
    · simp [h, Sym2.mem_iff]
    · simp [h, Sym2.mem_iff]

omit [Fintype V] in
theorem delta_appendEdge (k : ℕ) (ends : E → Sym2 V) (v w : V) (X : Finset V) :
    Delta k (appendEdge ends v w) X = addEdgeDeficiency (Delta k ends) v w X := by
  classical
  rw [Delta, edgesIn_appendEdge, Finset.card_disjSum]
  unfold addEdgeDeficiency Delta
  split_ifs
  · simp
    ring
  · simp

structure GoodCapacities (k : ℕ) (ends : E → Sym2 V) (g : V → ℤ) (s : ℤ) : Prop where
  nonneg : ∀ v, 0 ≤ g v
  deficiency : ∀ X, X.Nonempty → 0 ≤ Delta k ends X
  total : 2 * s < ∑ v, g v
  gamma : ∀ X, X.Nonempty → 0 ≤ deficiencyGamma (Delta k ends) g s X

theorem goodCapacities_appendEdge (k : ℕ) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (g : V → ℤ) (s : ℤ)
    (hg : GoodCapacities k ends g s) (hs : 0 < s) :
    ∃ v w, v ≠ w ∧ 0 < g v ∧ 0 < g w ∧
      GoodCapacities k (appendEdge ends v w) (consumePair g v w) (s - 1) := by
  obtain ⟨v, w, hvw, hv, hw, hcrit, hcruc⟩ := augmentation_endpoints (Delta k ends) g s
    (delta_submodular k ends) hg.deficiency (delta_singleton k ends hloop)
    hg.nonneg hs hg.total hg.gamma
  refine ⟨v, w, hvw, hv, hw, ?_⟩
  constructor
  · exact consumePair_nonneg g hg.nonneg hvw hv hw
  · intro X hX
    rw [delta_appendEdge]
    exact addEdgeDeficiency_nonneg (Delta k ends) v w hg.deficiency hcrit X hX
  · rw [consumePair_total]
    have h := hg.total
    omega
  · intro X hX
    have he : Delta k (appendEdge ends v w) = addEdgeDeficiency (Delta k ends) v w := by
      funext Y
      exact delta_appendEdge k ends v w Y
    rw [he]
    exact gamma_augmentation_nonneg (Delta k ends) g s v w hg.gamma hcruc X hX

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

theorem deleted_gamma_identity (k : ℕ) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (X : Finset (DeletedVertex v)) :
    deficiencyGamma (Delta k (deletedEnds ends v)) (deletedCapacity ends v)
      ((incidentDegree ends v : ℤ) - k) X =
      Delta k ends (insert v (liftDeletedSet v X)) := by
  rw [deficiencyGamma, outsideMass_eq, deletedCapacity_total ends hloop v]
  simp only [Delta]
  rw [internal_insert_count ends hloop v X,
    Finset.card_insert_of_notMem (center_not_liftDeletedSet v X)]
  simp only [liftDeletedSet, Finset.card_map, Nat.cast_add, Nat.cast_one]
  ring

theorem deleted_goodCapacities (k s : ℕ) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V)
    (hD : ∀ X, X.Nonempty → 0 ≤ Delta k ends X)
    (hdegree : incidentDegree ends v = k + s) (hs : s < k) :
    GoodCapacities k (deletedEnds ends v) (deletedCapacity ends v) (s : ℤ) := by
  constructor
  · exact deletedCapacity_nonneg ends v
  · intro X hX
    rw [delta_deleted]
    apply hD
    exact hX.map (f := deletedVertexEmbedding v)
  · rw [deletedCapacity_total ends hloop v, hdegree]
    exact_mod_cast (by omega : 2 * s < k + s)
  · intro X _
    have h := deleted_gamma_identity k ends hloop v X
    have hcast : (incidentDegree ends v : ℤ) - k = (s : ℤ) := by omega
    rw [hcast] at h
    rw [h]
    exact hD _ (Finset.insert_nonempty _ _)

omit [Fintype V] in
theorem remainingEdge_card (ends : E → Sym2 V) (v : V) :
    Fintype.card (RemainingEdge ends v) + incidentDegree ends v = Fintype.card E := by
  classical
  have h := Fintype.card_subtype_compl (fun e : E => v ∈ ends e)
  have hle := Fintype.card_subtype_le (fun e : E => v ∈ ends e)
  change Fintype.card (RemainingEdge ends v) = Fintype.card E - incidentDegree ends v at h
  change incidentDegree ends v ≤ Fintype.card E at hle
  omega

theorem deletedVertex_card (v : V) :
    Fintype.card (DeletedVertex v) + 1 = Fintype.card V := by
  have h := Fintype.card_subtype_compl (fun w : V => w = v)
  simp only [Fintype.card_subtype_eq] at h
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  change Fintype.card (DeletedVertex v) = Fintype.card V - 1 at h
  omega

theorem augmented_deleted_critical (k s : ℕ) (ends : E → Sym2 V)
    (v : V) (hcrit : IsCritical k ends) (hdegree : incidentDegree ends v = k + s)
    {J : Type*} [Fintype J] (a : J → Sym2 (DeletedVertex v)) (hJ : Fintype.card J = s) :
    IsCritical k (Sum.elim (deletedEnds ends v) a) := by
  have he := remainingEdge_card ends v
  have hv := deletedVertex_card v
  unfold IsCritical at hcrit ⊢
  simp only [Fintype.card_sum, Nat.cast_add, hJ]
  have hei : (Fintype.card (RemainingEdge ends v) : ℤ) + incidentDegree ends v = Fintype.card E := by exact_mod_cast he
  have hvi : (Fintype.card (DeletedVertex v) : ℤ) + 1 = Fintype.card V := by exact_mod_cast hv
  have hdi : (incidentDegree ends v : ℤ) = k + s := by exact_mod_cast hdegree
  nlinarith

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical

namespace NashWilliams61.TreePacking.NWFresh

variable {V E J : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype J]

theorem oldLift_forest (ends : E → Sym2 V) (v : V) (a : J → Sym2 (DeletedVertex v))
    (T : Finset (RemainingEdge ends v ⊕ J))
    (hT : IsSpanningTree (Sum.elim (deletedEnds ends v) a) T) :
    IsForest ends (oldLift ends v T) := by
  have hsub : (oldSelected ends v T).image Sum.inl ⊆ T := by
    intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hx).2
  have hsmall := forest_mono (Sum.elim (deletedEnds ends v) a) hsub hT.2.2.2.1
  have hdel : IsForest (deletedEnds ends v) (oldSelected ends v T) :=
    forest_of_image _ _ Sum.inl Sum.inl_injective (fun _ => rfl) hsmall
  obtain ⟨w, _⟩ := hT.2.1
  let r : V → DeletedVertex v := fun z => if h : z ≠ v then ⟨z,h⟩ else w
  have hr : Function.LeftInverse r (Subtype.val : DeletedVertex v → V) := by
    intro z
    simp [r, z.property]
  have hm := forest_vertex_map (deletedEnds ends v) Subtype.val r hr hdel
  exact forest_image _ ends Subtype.val Subtype.val_injective
    (fun e => (deletedEnds_map ends v e).symm) hm

theorem nonincident_expanded_mem (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (T : Finset (RemainingEdge ends v ⊕ J)) {e : E}
    (he : e ∈ expandedEdges ends v a f T) (hn : v ∉ ends e) : e ∈ oldLift ends v T := by
  rcases Finset.mem_union.mp he with ho | hnew
  · exact ho
  · exact False.elim (hn (newLift_incident ends v a f T hnew))

theorem selected_lift_tree (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (a : J → Sym2 (DeletedVertex v))
    (f : EndpointOccurrence v a → IncidentEdge ends v)
    (hf : ∀ p, otherEndpoint ends hloop v (f p) = p.1)
    (T : Finset (RemainingEdge ends v ⊕ J))
    (hT : IsSpanningTree (Sum.elim (deletedEnds ends v) a) T)
    (hnew : (newSelected ends v T).Nonempty) :
    ∃ U : Finset E, oldLift ends v T ⊆ U ∧ U ⊆ expandedEdges ends v a f T ∧
      IsSpanningTree ends U ∧
      (U.filter fun e => v ∈ ends e).card = (newSelected ends v T).card + 1 := by
  have hc := expanded_connected ends hloop v a f hf T hT hnew
  have : Nonempty V := hc.nonempty
  obtain ⟨U, hold, hU, ht⟩ := connected_exists_forest_tree ends
    (show oldLift ends v T ⊆ expandedEdges ends v a f T from Finset.subset_union_left)
    (oldLift_forest ends v a T hT) hc
  have hu : IsSpanningTree ends U := (treeOn_univ_iff ends U).mp ht
  refine ⟨U, hold, hU, hu, ?_⟩
  have hfilter : U.filter (fun e => v ∉ ends e) = oldLift ends v T := by
    ext e
    constructor
    · intro he
      obtain ⟨he, hn⟩ := Finset.mem_filter.mp he
      exact nonincident_expanded_mem ends v a f T (hU he) hn
    · intro he
      exact Finset.mem_filter.mpr ⟨hold he, oldLift_not_incident ends v T he⟩
  have hparts := Finset.card_filter_add_card_filter_not (s := U) (fun e => v ∈ ends e)
  rw [hfilter, oldLift_card] at hparts
  have huCard := spanningTree_card ends hu
  have htCard := spanningTree_card (Sum.elim (deletedEnds ends v) a) hT
  have hsplit := selected_card ends v T
  have hv := deletedVertex_card v
  omega

theorem expanded_eq_old_of_new_empty (ends : E → Sym2 V) (v : V)
    (a : J → Sym2 (DeletedVertex v)) (f : EndpointOccurrence v a → IncidentEdge ends v)
    (T : Finset (RemainingEdge ends v ⊕ J)) (hnew : newSelected ends v T = ∅) :
    expandedEdges ends v a f T = oldLift ends v T := by
  have hn : newLift ends v a f T = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨p, hp, _⟩ := Finset.mem_image.mp he
    have hj : p.2.val ∈ newSelected ends v T := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
    rw [hnew] at hj
    exact Finset.notMem_empty _ hj
  simp only [expandedEdges, hn, Finset.union_empty]

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical

namespace NashWilliams61.TreePacking.NWFresh

variable {V E J : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype J]

theorem attach_incident_tree (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (a : J → Sym2 (DeletedVertex v))
    (f : EndpointOccurrence v a → IncidentEdge ends v)
    (hf : ∀ p, otherEndpoint ends hloop v (f p) = p.1)
    (T : Finset (RemainingEdge ends v ⊕ J))
    (hT : IsSpanningTree (Sum.elim (deletedEnds ends v) a) T)
    (hnew : newSelected ends v T = ∅) (e : IncidentEdge ends v) :
    IsSpanningTree ends (insert e.val (oldLift ends v T)) := by
  let : Nonempty V := ⟨v⟩
  have hroot : (edgeGraph ends (insert e.val (oldLift ends v T))).Reachable v
      (otherEndpoint ends hloop v e).val := by
    apply SimpleGraph.Adj.reachable
    apply (edgeGraph_adj_iff _ _ _ _).mpr
    exact ⟨⟨e.val, Finset.mem_insert_self _ _, (otherEndpoint_spec ends hloop v e).symm⟩,
      Ne.symm (otherEndpoint ends hloop v e).property⟩
  have hc : (edgeGraph ends (insert e.val (oldLift ends v T))).Connected := by
    have hall : ∀ z, (edgeGraph ends (insert e.val (oldLift ends v T))).Reachable v z := by
      intro z
      by_cases hz : z = v
      · subst z
        exact SimpleGraph.Reachable.rfl
      · have hr := expanded_reachable ends hloop v a f hf T
          (hT.2.2.2.2 (otherEndpoint ends hloop v e) (Finset.mem_univ _) ⟨z,hz⟩ (Finset.mem_univ _))
        rw [expanded_eq_old_of_new_empty ends v a f T hnew] at hr
        exact hroot.trans (hr.mono (edgeGraph_mono ends (Finset.subset_insert _ _)))
    constructor
    intro x y
    exact (hall x).symm.trans (hall y)
  apply tree_of_connected_card ends _ hc
  have hen : e.val ∉ oldLift ends v T := by
    intro he
    exact oldLift_not_incident ends v T he e.property
  rw [Finset.card_insert_of_notMem hen, oldLift_card]
  have hsplit := selected_card ends v T
  have htCard := spanningTree_card (Sum.elim (deletedEnds ends v) a) hT
  have hv := deletedVertex_card v
  rw [hnew, Finset.card_empty] at hsplit
  omega

omit [Fintype V] [Fintype J] in
theorem oldLift_pairwise_disjoint (ends : E → Sym2 V) (v : V)
    {T U : Finset (RemainingEdge ends v ⊕ J)} (hTU : Disjoint T U) :
    Disjoint (oldLift ends v T) (oldLift ends v U) := by
  apply Finset.disjoint_left.mpr
  intro e heT heU
  obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp heT
  obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp heU
  have hxy : x = y := Subtype.ext (hxe.trans hye.symm)
  subst y
  exact Finset.disjoint_left.mp hTU ((Finset.mem_filter.mp hx).2) ((Finset.mem_filter.mp hy).2)

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {I E : Type*} [Fintype I] [DecidableEq I] [DecidableEq E]

theorem unused_label_budget (B : Finset E) (U : I → Finset E) (A : Finset I)
    (r : I → ℕ) (s : ℕ) (hB : B.card = Fintype.card I + s)
    (hsum : (∑ i, r i) ≤ s)
    (hactive : ∀ i ∈ A, (U i ∩ B).card ≤ r i + 1)
    (hinactive : ∀ i, i ∉ A → U i ∩ B = ∅) :
    (Finset.univ \ A).card ≤ (B \ Finset.univ.biUnion U).card := by
  classical
  have hinter : B ∩ Finset.univ.biUnion U =
      Finset.univ.biUnion (fun i => U i ∩ B) := by
    ext e
    simp only [Finset.mem_inter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    aesop
  have hcount : (B ∩ Finset.univ.biUnion U).card ≤ s + A.card := by
    rw [hinter]
    apply Finset.card_biUnion_le.trans
    calc
      (∑ i, (U i ∩ B).card) ≤ ∑ i, (r i + if i ∈ A then 1 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i ∈ A
        · simpa only [if_pos hi] using hactive i hi
        · simp only [hinactive i hi, Finset.card_empty, if_neg hi, add_zero, Nat.zero_le]
      _ = (∑ i, r i) + A.card := by simp [Finset.sum_add_distrib]
      _ ≤ s + A.card := Nat.add_le_add_right hsum _
  have hsplit := Finset.card_sdiff_add_card_inter B (Finset.univ.biUnion U)
  have hAc : A.card ≤ Fintype.card I := Finset.card_le_univ A
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  omega

theorem unused_label_injection (B : Finset E) (U : I → Finset E) (A : Finset I)
    (r : I → ℕ) (s : ℕ) (hB : B.card = Fintype.card I + s)
    (hsum : (∑ i, r i) ≤ s)
    (hactive : ∀ i ∈ A, (U i ∩ B).card ≤ r i + 1)
    (hinactive : ∀ i, i ∉ A → U i ∩ B = ∅) :
    ∃ f : {i : I // i ∉ A} → E, Function.Injective f ∧
      ∀ i, f i ∈ B ∧ ∀ j, f i ∉ U j := by
  classical
  let C := B \ Finset.univ.biUnion U
  have hc : Fintype.card {i : I // i ∉ A} ≤ Fintype.card {e : E // e ∈ C} := by
    have h := unused_label_budget B U A r s hB hsum hactive hinactive
    have he : Finset.univ.filter (fun i : I => i ∉ A) = Finset.univ \ A := by
      ext i
      simp
    simpa only [Fintype.card_subtype, he, Fintype.card_coe, C] using h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hc
  refine ⟨fun i => (f i).val, ?_, ?_⟩
  · intro i j hij
    exact f.injective (Subtype.ext hij)
  · intro i
    have hi := Finset.mem_sdiff.mp (f i).property
    refine ⟨hi.1, ?_⟩
    intro j hj
    exact hi.2 (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩)

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical

namespace NashWilliams61.TreePacking.NWFresh

variable {V E J I : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype J] [Fintype I]

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem newSelected_disjoint (ends : E → Sym2 V) (v : V)
    {T U : Finset (RemainingEdge ends v ⊕ J)} (hTU : Disjoint T U) :
    Disjoint (newSelected ends v T) (newSelected ends v U) := by
  apply Finset.disjoint_left.mpr
  intro j hjT hjU
  exact Finset.disjoint_left.mp hTU ((Finset.mem_filter.mp hjT).2) ((Finset.mem_filter.mp hjU).2)

omit [Fintype V] [Fintype E] [DecidableEq V] in
theorem sum_newSelected_le (ends : E → Sym2 V) (v : V)
    (T : I → Finset (RemainingEdge ends v ⊕ J))
    (hT : ∀ i j, i ≠ j → Disjoint (T i) (T j)) :
    (∑ i, (newSelected ends v (T i)).card) ≤ Fintype.card J := by
  have hd : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint (fun i => newSelected ends v (T i)) := by
    intro i _ j _ hij
    exact newSelected_disjoint ends v (hT i j hij)
  rw [← Finset.card_biUnion hd]
  exact Finset.card_le_univ _

noncomputable def activeTrees (ends : E → Sym2 V) (v : V)
    (T : I → Finset (RemainingEdge ends v ⊕ J)) : Finset I :=
  Finset.univ.filter fun i => (newSelected ends v (T i)).Nonempty

theorem select_lift_family (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (a : J → Sym2 (DeletedVertex v))
    (f : EndpointOccurrence v a → IncidentEdge ends v) (hf : Function.Injective f)
    (hend : ∀ p, otherEndpoint ends hloop v (f p) = p.1)
    (T : I → Finset (RemainingEdge ends v ⊕ J))
    (hdis : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (htree : ∀ i, IsSpanningTree (Sum.elim (deletedEnds ends v) a) (T i)) :
    ∃ U : I → Finset E,
      (∀ i, oldLift ends v (T i) ⊆ U i ∧ U i ⊆ expandedEdges ends v a f (T i)) ∧
      (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (∀ i ∈ activeTrees ends v T, IsSpanningTree ends (U i) ∧
        ((U i).filter fun e => v ∈ ends e).card = (newSelected ends v (T i)).card + 1) ∧
      (∀ i, i ∉ activeTrees ends v T → U i = oldLift ends v (T i)) := by
  have hex : ∀ i, ∃ U : Finset E,
      oldLift ends v (T i) ⊆ U ∧ U ⊆ expandedEdges ends v a f (T i) ∧
      (i ∈ activeTrees ends v T → IsSpanningTree ends U ∧
        (U.filter fun e => v ∈ ends e).card = (newSelected ends v (T i)).card + 1) ∧
      (i ∉ activeTrees ends v T → U = oldLift ends v (T i)) := by
    intro i
    by_cases hi : i ∈ activeTrees ends v T
    · have hn : (newSelected ends v (T i)).Nonempty := (Finset.mem_filter.mp hi).2
      obtain ⟨U, ho, hu, ht, hc⟩ := selected_lift_tree ends hloop v a f hend (T i) (htree i) hn
      exact ⟨U, ho, hu, fun _ => ⟨ht,hc⟩, fun h => False.elim (h hi)⟩
    · exact ⟨oldLift ends v (T i), Finset.Subset.refl _, Finset.subset_union_left,
        fun h => False.elim (hi h), fun _ => rfl⟩
  choose U hU using hex
  refine ⟨U, fun i => ⟨(hU i).1, (hU i).2.1⟩, ?_, ?_, ?_⟩
  · intro i j hij
    exact (expanded_disjoint ends v a f hf (hdis i j hij)).mono (hU i).2.1 (hU j).2.1
  · intro i hi
    exact (hU i).2.2.1 hi
  · intro i hi
    exact (hU i).2.2.2 hi

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {I E : Type*} [DecidableEq I] [DecidableEq E]

def attachFreeLabels (A : Finset I) (U : I → Finset E) (f : {i : I // i ∉ A} → E)
    (i : I) : Finset E := if h : i ∈ A then U i else insert (f ⟨i,h⟩) (U i)

theorem attachFreeLabels_disjoint (A : Finset I) (U : I → Finset E)
    (f : {i : I // i ∉ A} → E) (hf : Function.Injective f)
    (hfree : ∀ i j, f i ∉ U j) (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j)) :
    ∀ i j, i ≠ j → Disjoint (attachFreeLabels A U f i) (attachFreeLabels A U f j) := by
  intro i j hij
  have hd := hU i j hij
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A
  · simpa only [attachFreeLabels, dif_pos hi, dif_pos hj] using hd
  · simp only [attachFreeLabels, dif_pos hi, dif_neg hj, Finset.disjoint_insert_right]
    exact ⟨hfree ⟨j,hj⟩ i, hd⟩
  · simp only [attachFreeLabels, dif_neg hi, dif_pos hj, Finset.disjoint_insert_left]
    exact ⟨hfree ⟨i,hi⟩ j, hd⟩
  · simp only [attachFreeLabels, dif_neg hi, dif_neg hj, Finset.disjoint_insert_left,
      Finset.disjoint_insert_right, Finset.mem_insert, not_or]
    refine ⟨⟨?_, hfree ⟨j,hj⟩ i⟩, hfree ⟨i,hi⟩ j, hd⟩
    intro he
    exact hij (congrArg Subtype.val (hf he)).symm

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

theorem partition_delta_sum (k : ℕ) (ends : E → Sym2 V)
    (P : Finpartition (Finset.univ : Finset V)) :
    (∑ X ∈ P.parts, Delta k ends X) =
      (k : ℤ) * ((Fintype.card V : ℤ) - P.parts.card) -
      ∑ X ∈ P.parts, ((edgesIn ends X).card : ℤ) := by
  have hc : (∑ X ∈ P.parts, (X.card : ℤ)) = (Fintype.card V : ℤ) := by
    exact_mod_cast P.sum_card_parts
  simp only [Delta, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hc]

theorem critical_admissible_of_delta (k : ℕ) (ends : E → Sym2 V)
    (hc : IsCritical k ends) (hd : ∀ X : Finset V, X.Nonempty → 0 ≤ Delta k ends X) :
    IsAdmissible k ends := by
  intro P
  have hn : 0 ≤ ∑ X ∈ P.parts, Delta k ends X := by
    exact Finset.sum_nonneg (fun X hX => hd X (P.nonempty_of_mem_parts hX))
  rw [partition_delta_sum] at hn
  have he : (∑ X ∈ P.parts, ((edgesIn ends X).card : ℤ)) +
      ((crossing ends P).card : ℤ) = Fintype.card E := by
    exact_mod_cast partition_edge_count ends P
  change (Fintype.card E : ℤ) = (k : ℤ) * ((Fintype.card V : ℤ) - 1) at hc
  change (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ ((crossing ends P).card : ℤ)
  nlinarith

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

noncomputable def oneBlockPartition (X : Finset V) (hX : X.Nonempty) :
    Finpartition (Finset.univ : Finset V) :=
  (⊥ : Finpartition (Finset.univ \ X)).extend hX.ne_empty
    Finset.sdiff_disjoint (by simp)

theorem oneBlockPartition_card (X : Finset V) (hX : X.Nonempty) :
    (oneBlockPartition X hX).parts.card = Fintype.card V - X.card + 1 := by
  rw [oneBlockPartition, Finpartition.card_extend, Finpartition.card_bot]
  rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]

theorem oneBlockPartition_internal (ends : E → Sym2 V) (hl : ∀ e, ¬ (ends e).IsDiag)
    (X : Finset V) (hX : X.Nonempty) :
    (∑ Y ∈ (oneBlockPartition X hX).parts, (edgesIn ends Y).card) = (edgesIn ends X).card := by
  have hnot : X ∉ (⊥ : Finpartition (Finset.univ \ X)).parts := by
    intro hh
    have hx := (⊥ : Finpartition (Finset.univ \ X)).le hh
    obtain ⟨v, hv⟩ := hX
    exact (Finset.mem_sdiff.mp (hx hv)).2 hv
  rw [oneBlockPartition, Finpartition.extend_parts, Finset.sum_insert hnot]
  have hz : ∑ Y ∈ (⊥ : Finpartition (Finset.univ \ X)).parts, (edgesIn ends Y).card = 0 := by
    apply Finset.sum_eq_zero
    intro Y hY
    obtain ⟨v, _, rfl⟩ := Finpartition.mem_bot_iff.mp hY
    rw [edgesIn_singleton_eq_empty ends hl v]
    rfl
  rw [hz, add_zero]

theorem critical_delta_of_admissible (k : ℕ) (ends : E → Sym2 V)
    (hl : ∀ e, ¬ (ends e).IsDiag) (hc : IsCritical k ends) (ha : IsAdmissible k ends)
    (X : Finset V) (hX : X.Nonempty) : 0 ≤ Delta k ends X := by
  have hp := ha (oneBlockPartition X hX)
  have he := partition_edge_count ends (oneBlockPartition X hX)
  rw [oneBlockPartition_internal ends hl X hX] at he
  change (k : ℤ) * (((oneBlockPartition X hX).parts.card : ℤ) - 1) ≤ _ at hp
  rw [oneBlockPartition_card] at hp
  have hcard : X.card ≤ Fintype.card V := Finset.card_le_univ X
  rw [Nat.cast_add, Nat.cast_sub hcard, Nat.cast_one] at hp
  change (Fintype.card E : ℤ) = (k : ℤ) * ((Fintype.card V : ℤ) - 1) at hc
  have he' : ((edgesIn ends X).card : ℤ) +
      ((crossing ends (oneBlockPartition X hX)).card : ℤ) = Fintype.card E := by
    exact_mod_cast he
  dsimp [Delta]
  nlinarith

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

theorem internal_erase_center (ends : E → Sym2 V) (v : V) :
    (edgesIn ends (Finset.univ.erase v)).card = Fintype.card (RemainingEdge ends v) := by
  classical
  rw [Fintype.card_subtype]
  congr 1
  ext e
  simp only [mem_edgesIn_iff, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h hv
    exact (Finset.mem_erase.mp (h v hv)).1 rfl
  · intro h w hw
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro he
    exact h (he ▸ hw)

theorem admissible_degree_lower (k : ℕ) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (ha : IsAdmissible k ends)
    (hn : 2 ≤ Fintype.card V) (v : V) : k ≤ incidentDegree ends v := by
  classical
  have hX : (Finset.univ.erase v).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    omega
  let P := oneBlockPartition (Finset.univ.erase v) hX
  have hP : P.parts.card = 2 := by
    rw [oneBlockPartition_card, Finset.card_erase_of_mem (Finset.mem_univ v), Finset.card_univ]
    omega
  have hp := ha P
  change (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ ((crossing ends P).card : ℤ) at hp
  rw [hP] at hp
  norm_num at hp
  have he := partition_edge_count ends P
  change (∑ Y ∈ (oneBlockPartition (Finset.univ.erase v) hX).parts, (edgesIn ends Y).card) +
    (crossing ends P).card = Fintype.card E at he
  rw [oneBlockPartition_internal ends hloop, internal_erase_center] at he
  have hd := remainingEdge_card ends v
  have hcross : (crossing ends P).card = incidentDegree ends v := by omega
  rw [hcross] at hp
  exact_mod_cast hp

theorem critical_reduction_vertex (k : ℕ) (hk : 0 < k) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (ha : IsAdmissible k ends)
    (hc : IsCritical k ends) (hn : 2 ≤ Fintype.card V) :
    ∃ v s, s < k ∧ incidentDegree ends v = k + s ∧
      GoodCapacities k (deletedEnds ends v) (deletedCapacity ends v) (s : ℤ) := by
  obtain ⟨v, hv⟩ := critical_low_degree k hk ends hloop hc
  have hlo := admissible_degree_lower k ends hloop ha hn v
  let s := incidentDegree ends v - k
  have hs : s < k := by dsimp [s]; omega
  have hd : incidentDegree ends v = k + s := by dsimp [s]; omega
  refine ⟨v, s, hs, hd, ?_⟩
  exact deleted_goodCapacities k s ends hloop v (critical_delta_of_admissible k ends hloop hc ha) hd hs

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E F : Type*} [Fintype V] [DecidableEq V] [Fintype E] [Fintype F]

omit [Fintype V] [DecidableEq V] in
theorem edgesIn_relabel (ends : E → Sym2 V) (ends' : F → Sym2 V)
    (e : E ≃ F) (he : ∀ x, ends' (e x) = ends x) (X : Finset V) :
    edgesIn ends' X = (edgesIn ends X).map e.toEmbedding := by
  classical
  ext y
  constructor
  · intro hy
    refine Finset.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    rw [mem_edgesIn_iff] at hy ⊢
    simpa only [← he (e.symm y), e.apply_symm_apply] using hy
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    rw [mem_edgesIn_iff] at hx ⊢
    change ∀ v ∈ ends' (e x), v ∈ X
    rw [he]
    exact hx

omit [Fintype V] [DecidableEq V] in
theorem delta_relabel (k : ℕ) (ends : E → Sym2 V) (ends' : F → Sym2 V)
    (e : E ≃ F) (he : ∀ x, ends' (e x) = ends x) (X : Finset V) :
    Delta k ends' X = Delta k ends X := by
  simp only [Delta, edgesIn_relabel ends ends' e he, Finset.card_map]

theorem goodCapacities_relabel (k : ℕ) (ends : E → Sym2 V) (ends' : F → Sym2 V)
    (e : E ≃ F) (he : ∀ x, ends' (e x) = ends x)
    (g : V → ℤ) (s : ℤ) (h : GoodCapacities k ends g s) :
    GoodCapacities k ends' g s := by
  have hd : Delta k ends' = Delta k ends := by
    funext X
    exact delta_relabel k ends ends' e he X
  exact ⟨h.nonneg, by simpa only [hd] using h.deficiency, h.total,
    by simpa only [hd] using h.gamma⟩

def endpointDegree {J : Type*} [Fintype J] (a : J → Sym2 V) (v : V) : ℤ :=
  ∑ j, if v ∈ a j then 1 else 0

omit [Fintype V] in
theorem endpointDegree_nonneg {J : Type*} [Fintype J] (a : J → Sym2 V) (v : V) :
    0 ≤ endpointDegree a v := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> omega

omit [Fintype V] in
theorem endpointDegree_sum {J K : Type*} [Fintype J] [Fintype K]
    (a : J → Sym2 V) (b : K → Sym2 V) (v : V) :
    endpointDegree (Sum.elim a b) v = endpointDegree a v + endpointDegree b v := by
  simp only [endpointDegree, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rfl

omit [Fintype V] in
theorem endpointDegree_pair {v w : V} (hvw : v ≠ w) (x : V) :
    endpointDegree (fun _ : Unit => s(v, w)) x =
      (if x = v then 1 else 0) + (if x = w then 1 else 0) := by
  by_cases hxv : x = v <;> by_cases hxw : x = w <;>
    simp_all [endpointDegree, Sym2.mem_iff]


end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

structure AugmentedGraph (k : ℕ) (ends : E → Sym2 V) (g : V → ℤ) (s : ℕ) where
  Added : Type
  [finiteAdded : Fintype Added]
  addedEnds : Added → Sym2 V
  residual : V → ℤ
  cardinality : Fintype.card Added = s
  loopless : ∀ j, ¬ (addedEnds j).IsDiag
  good : GoodCapacities k (Sum.elim ends addedEnds) residual 0
  capacity : ∀ v, residual v + endpointDegree addedEnds v = g v

attribute [instance] AugmentedGraph.finiteAdded

theorem finite_augmentation (k : ℕ) (s : ℕ) :
    ∀ {E : Type*} [Fintype E] (ends : E → Sym2 V),
      (∀ e, ¬ (ends e).IsDiag) → ∀ g : V → ℤ,
      GoodCapacities k ends g (s : ℤ) → Nonempty (AugmentedGraph k ends g s) := by
  induction s with
  | zero =>
    intro E _ ends _ g hg
    let a : Empty → Sym2 V := fun x => nomatch x
    have hgood : GoodCapacities k (Sum.elim ends a) g 0 := by
      apply goodCapacities_relabel k ends (Sum.elim ends a) (Equiv.sumEmpty E Empty).symm
        (fun _ => rfl) g 0
      exact hg
    exact ⟨{
      Added := Empty
      addedEnds := a
      residual := g
      cardinality := by simp
      loopless := fun x => nomatch x
      good := hgood
      capacity := by intro v; simp [endpointDegree]
    }⟩
  | succ s ih =>
    intro E _ ends hloop g hg
    obtain ⟨v, w, hvw, _, _, hnext⟩ := goodCapacities_appendEdge k ends hloop g
      ((s + 1 : ℕ) : ℤ) hg (by omega)
    have hn : GoodCapacities k (appendEdge ends v w) (consumePair g v w) (s : ℤ) := by
      simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using hnext
    obtain ⟨A⟩ := ih (appendEdge ends v w) (appendEdge_loopless ends hloop hvw)
      (consumePair g v w) hn
    let a : Unit ⊕ A.Added → Sym2 V := Sum.elim (fun _ => s(v, w)) A.addedEnds
    have he : ∀ x, Sum.elim ends a (Equiv.sumAssoc E Unit A.Added x) =
        Sum.elim (appendEdge ends v w) A.addedEnds x := by
      intro x
      rcases x with (e | u) | j <;> rfl
    have hgood : GoodCapacities k (Sum.elim ends a) A.residual 0 :=
      goodCapacities_relabel k _ _ (Equiv.sumAssoc E Unit A.Added) he _ _ A.good
    refine ⟨{
      Added := Unit ⊕ A.Added
      addedEnds := a
      residual := A.residual
      cardinality := by simp [Fintype.card_sum, A.cardinality, Nat.add_comm]
      loopless := ?_
      good := hgood
      capacity := ?_
    }⟩
    · intro j
      cases j with
      | inl u => simpa [a, Sym2.mk_isDiag_iff] using hvw
      | inr j => exact A.loopless j
    · intro x
      have hc := A.capacity x
      change A.residual x + endpointDegree (Sum.elim (fun _ : Unit => s(v, w)) A.addedEnds) x = g x
      rw [endpointDegree_sum, endpointDegree_pair hvw]
      unfold consumePair at hc
      omega

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V J E : Type*} [Fintype V] [DecidableEq V] [Fintype J] [Fintype E]

omit [Fintype V] [Fintype E] in
theorem endpointDegree_card (a : J → Sym2 V) (v : V) :
    endpointDegree a v = (Fintype.card {j : J // v ∈ a j} : ℤ) := by
  classical
  rw [Fintype.card_subtype]
  simp only [endpointDegree, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

omit [Fintype V] in
theorem endpoint_allocation (a : J → Sym2 V) (endpoint : E → V)
    (hcard : ∀ v, Fintype.card {j : J // v ∈ a j} ≤ Fintype.card {e : E // endpoint e = v}) :
    ∃ f : (Σ v : V, {j : J // v ∈ a j}) → E,
      Function.Injective f ∧ ∀ p, endpoint (f p) = p.1 := by
  classical
  have hex : ∀ v, Nonempty ({j : J // v ∈ a j} ↪ {e : E // endpoint e = v}) :=
    fun v => Function.Embedding.nonempty_of_card_le (hcard v)
  let emb (v : V) : {j : J // v ∈ a j} ↪ {e : E // endpoint e = v} := Classical.choice (hex v)
  let f : (Σ v : V, {j : J // v ∈ a j}) → E := fun p => (emb p.1 p.2).val
  refine ⟨f, ?_, ?_⟩
  · intro p q hpq
    rcases p with ⟨v, j⟩
    rcases q with ⟨w, l⟩
    have hvw : v = w := by
      calc
        v = endpoint (f ⟨v, j⟩) := (emb v j).property.symm
        _ = endpoint (f ⟨w, l⟩) := congrArg endpoint hpq
        _ = w := (emb w l).property
    subst w
    have hjl : j = l := (emb v).injective (Subtype.ext hpq)
    subst l
    rfl
  · intro p
    exact (emb p.1 p.2).property

theorem augmented_endpoint_allocation {k s : ℕ} (ends : E → Sym2 V) (g : V → ℤ)
    (A : AugmentedGraph k ends g s) {F : Type*} [Fintype F] (endpoint : F → V)
    (hg : ∀ v, g v = (Fintype.card {e : F // endpoint e = v} : ℤ)) :
    ∃ f : (Σ v : V, {j : A.Added // v ∈ A.addedEnds j}) → F,
      Function.Injective f ∧ ∀ p, endpoint (f p) = p.1 := by
  classical
  apply endpoint_allocation
  intro v
  have h := A.capacity v
  have hn := A.good.nonneg v
  rw [endpointDegree_card, hg v] at h
  omega

end NashWilliams61.TreePacking.NWFresh
end


section

namespace NashWilliams61.TreePacking.NWFresh

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]

theorem augmented_reduction_size (k s : ℕ) (hk : 0 < k) (ends : E → Sym2 V)
    (v : V) (hd : incidentDegree ends v = k + s)
    (A : AugmentedGraph k (deletedEnds ends v) (deletedCapacity ends v) s) :
    Fintype.card (DeletedVertex v) + Fintype.card (RemainingEdge ends v ⊕ A.Added) <
      Fintype.card V + Fintype.card E := by
  have hv := deletedVertex_card v
  have he := remainingEdge_card ends v
  simp only [Fintype.card_sum, A.cardinality]
  omega

theorem critical_vertex_reduction (k : ℕ) (hk : 0 < k) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (ha : IsAdmissible k ends)
    (hc : IsCritical k ends) (hn : 2 ≤ Fintype.card V) :
    ∃ (v : V) (s : ℕ) (A : AugmentedGraph k (deletedEnds ends v) (deletedCapacity ends v) s),
      s < k ∧ incidentDegree ends v = k + s ∧ Nonempty (DeletedVertex v) ∧
      (∀ e, ¬ (Sum.elim (deletedEnds ends v) A.addedEnds e).IsDiag) ∧
      IsCritical k (Sum.elim (deletedEnds ends v) A.addedEnds) ∧
      IsAdmissible k (Sum.elim (deletedEnds ends v) A.addedEnds) ∧
      Fintype.card (DeletedVertex v) + Fintype.card (RemainingEdge ends v ⊕ A.Added) <
        Fintype.card V + Fintype.card E := by
  obtain ⟨v, s, hs, hd, hg⟩ := critical_reduction_vertex k hk ends hloop ha hc hn
  obtain ⟨A⟩ := finite_augmentation k s (deletedEnds ends v) (deletedEnds_loopless ends hloop v)
    (deletedCapacity ends v) hg
  have hcrit := augmented_deleted_critical k s ends v hc hd A.addedEnds A.cardinality
  refine ⟨v, s, A, hs, hd, ?_, ?_, hcrit, ?_, augmented_reduction_size k s hk ends v hd A⟩
  · apply Fintype.card_pos_iff.mp
    have hv := deletedVertex_card v
    omega
  · intro e
    cases e with
    | inl e => exact deletedEnds_loopless ends hloop v e
    | inr e => exact A.loopless e
  · exact critical_admissible_of_delta k _ hcrit A.good.deficiency

theorem critical_reduction_endpoint_allocation {k s : ℕ} (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V)
    (A : AugmentedGraph k (deletedEnds ends v) (deletedCapacity ends v) s) :
    ∃ f : (Σ w : DeletedVertex v, {j : A.Added // w ∈ A.addedEnds j}) → IncidentEdge ends v,
      Function.Injective f ∧ ∀ p, otherEndpoint ends hloop v (f p) = p.1 := by
  exact augmented_endpoint_allocation _ _ A (otherEndpoint ends hloop v)
    (deletedCapacity_fiber ends hloop v)

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical

namespace NashWilliams61.TreePacking.NWFresh

variable {V E J : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype J]

theorem simultaneous_lift (k s : ℕ) (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V) (a : J → Sym2 (DeletedVertex v))
    (hdegree : incidentDegree ends v = k + s) (hJ : Fintype.card J = s)
    (f : EndpointOccurrence v a → IncidentEdge ends v) (hf : Function.Injective f)
    (hend : ∀ p, otherEndpoint ends hloop v (f p) = p.1)
    (hpack : HasKTrees k (Sum.elim (deletedEnds ends v) a)) : HasKTrees k ends := by
  obtain ⟨T, hdis, htree⟩ := hpack
  obtain ⟨U, _, hUdis, hactive, hinactive⟩ := select_lift_family ends hloop v a f hf hend T hdis htree
  let A := activeTrees ends v T
  let B := Finset.univ.filter fun e : E => v ∈ ends e
  let r := fun i => (newSelected ends v (T i)).card
  have hB : B.card = Fintype.card (Fin k) + s := by
    have hb : B.card = incidentDegree ends v := by
      simp only [B, incidentDegree, Fintype.card_subtype]
    rw [hb, hdegree, Fintype.card_fin]
  have hsum : (∑ i, r i) ≤ s := by
    simpa only [hJ] using sum_newSelected_le ends v T hdis
  have hfilter : ∀ i, U i ∩ B = (U i).filter (fun e => v ∈ ends e) := by
    intro i
    ext e
    simp [B]
  have hact : ∀ i ∈ A, (U i ∩ B).card ≤ r i + 1 := by
    intro i hi
    rw [hfilter]
    exact (hactive i hi).2.le
  have hin : ∀ i, i ∉ A → U i ∩ B = ∅ := by
    intro i hi
    rw [hinactive i hi]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨ho, hb⟩ := Finset.mem_inter.mp he
    exact oldLift_not_incident ends v (T i) ho (Finset.mem_filter.mp hb).2
  obtain ⟨q, hq, hfree⟩ := unused_label_injection B U A r s hB hsum hact hin
  refine ⟨attachFreeLabels A U q, attachFreeLabels_disjoint A U q hq
    (fun i j => (hfree i).2 j) hUdis, ?_⟩
  intro i
  by_cases hi : i ∈ A
  · simpa only [attachFreeLabels, dif_pos hi] using (hactive i hi).1
  · have hnew : newSelected ends v (T i) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hn
      exact hi (by simp [A, activeTrees, hn])
    have he : v ∈ ends (q ⟨i,hi⟩) := (Finset.mem_filter.mp (hfree ⟨i,hi⟩).1).2
    have ht := attach_incident_tree ends hloop v a f hend (T i) (htree i) hnew ⟨q ⟨i,hi⟩,he⟩
    simpa only [attachFreeLabels, dif_neg hi, hinactive i hi] using ht

theorem lift_augmented_packing {k s : ℕ} (ends : E → Sym2 V)
    (hloop : ∀ e, ¬ (ends e).IsDiag) (v : V)
    (hd : incidentDegree ends v = k + s)
    (A : AugmentedGraph k (deletedEnds ends v) (deletedCapacity ends v) s)
    (hpack : HasKTrees k (Sum.elim (deletedEnds ends v) A.addedEnds)) : HasKTrees k ends := by
  obtain ⟨f, hf, hend⟩ := critical_reduction_endpoint_allocation ends hloop v A
  exact simultaneous_lift k s ends hloop v A.addedEnds hd A.cardinality f hf hend hpack

end NashWilliams61.TreePacking.NWFresh
end


section

open Classical
namespace NashWilliams61.TreePacking.NWFresh

theorem admissible_hasKTrees :
    ∀ {V E : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype E] [DecidableEq E]
      (ends : E → Sym2 V), (∀ e, ¬ (ends e).IsDiag) →
      ∀ k : ℕ, 0 < k → IsAdmissible k ends → HasKTrees k ends := by
  have main : ∀ N : ℕ,
      ∀ {V E : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype E] [DecidableEq E]
        (ends : E → Sym2 V), (∀ e, ¬ (ends e).IsDiag) →
        ∀ k : ℕ, 0 < k → IsAdmissible k ends →
          Fintype.card V + Fintype.card E ≤ N → HasKTrees k ends := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro V E _ _ _ _ _ ends hl k hk ha hN
      by_cases h1 : Fintype.card V = 1
      · exact singleton_packing k ends h1
      have hn : 2 ≤ Fintype.card V := by have := Fintype.card_pos (α := V); omega
      by_cases hP : ∃ P : Finpartition (Finset.univ : Finset V),
          1 < P.parts.card ∧ P.parts.card < Fintype.card V ∧ IsCriticalPartition k ends P
      · obtain ⟨P, hp1, hp2, hpc⟩ := hP
        apply packing_glue k ends P
        · intro X
          have : Nonempty X.val := ⟨⟨(P.nonempty_of_mem_parts X.property).choose,
            (P.nonempty_of_mem_parts X.property).choose_spec⟩⟩
          exact ih (Fintype.card X.val + Fintype.card (InternalEdge ends X.val))
            (lt_of_lt_of_le (restriction_size_lt ends P hp1 X) hN)
            (restrictedEnds ends X.val) (restrictedEnds_loopless ends hl X.val) k hk
            (restriction_admissible k ends ha P hpc X.val X.property) le_rfl
        · have : Nonempty (PartitionVertex P) := Fintype.card_pos_iff.mp (by
            simpa only [Fintype.card_coe] using (show 0 < P.parts.card by omega))
          exact ih (Fintype.card (PartitionVertex P) + Fintype.card (CrossingEdge ends P))
            (lt_of_lt_of_le (quotient_size_lt ends P hp2) hN)
            (quotientNativeEnds ends P) (quotientNativeEnds_loopless ends P) k hk
            (quotient_admissible k ends ha P) le_rfl
      · by_cases hc : IsCritical k ends
        · obtain ⟨v, s, A, _, hd, hne, hloop, _, hadm, hsize⟩ :=
            critical_vertex_reduction k hk ends hl ha hc hn
          have : Nonempty (DeletedVertex v) := hne
          have hpack := ih (Fintype.card (DeletedVertex v) + Fintype.card (RemainingEdge ends v ⊕ A.Added))
            (lt_of_lt_of_le hsize hN) (Sum.elim (deletedEnds ends v) A.addedEnds)
            hloop k hk hadm le_rfl
          exact lift_augmented_packing ends hl v hd A hpack
        · have hslack := no_tight_partition_slack k ends hl ha hc (by
            intro P hp hh
            exact hP ⟨P, hh.1, hh.2, hp⟩)
          have hepos : 0 < Fintype.card E := by
            have ht := admissible_total k ends ha
            have hk' : (1 : ℤ) ≤ k := by omega
            have hn' : (1 : ℤ) ≤ (Fintype.card V : ℤ) - 1 := by omega
            have hm : (1 : ℤ) ≤ (k : ℤ) * ((Fintype.card V : ℤ) - 1) := by nlinarith
            omega
          obtain ⟨e⟩ := Fintype.card_pos_iff.mp hepos
          have hcard : Fintype.card (DeletedEdge e) < Fintype.card E := by
            exact Fintype.card_lt_of_injective_not_surjective Subtype.val Subtype.val_injective
              (by intro hs; obtain ⟨a, ha'⟩ := hs e; exact a.property ha')
          have hpack := ih (Fintype.card V + Fintype.card (DeletedEdge e))
            (lt_of_lt_of_le (by omega) hN) (fun f : DeletedEdge e => ends f.val)
            (fun f => hl f.val) k hk (delete_slack_admissible k ends hslack e) le_rfl
          exact hasKTrees_label_image k (fun f : DeletedEdge e => ends f.val) ends Subtype.val
            Subtype.val_injective (fun _ => rfl) hpack
  intro V E _ _ _ _ _ ends hl k hk ha
  exact main (Fintype.card V + Fintype.card E) ends hl k hk ha le_rfl

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn Classical
namespace NashWilliams61.TreePacking.NWFresh
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem packing_admissible (ends : E → Sym2 V) (k : ℕ)
    (T : Fin k → Finset E) (hd : ∀ i j, i ≠ j → Disjoint (T i) (T j))
    (ht : ∀ i, IsSpanningTree ends (T i)) : IsAdmissible k ends := by
  intro P
  let C : Fin k → Finset E := fun i => (T i).filter (· ∈ crossing ends P)
  have hdis : ((Finset.univ : Finset (Fin k)) : Set (Fin k)).PairwiseDisjoint C := by
    intro i _ j _ hij
    exact (hd i j hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hsub : Finset.univ.biUnion C ⊆ crossing ends P := by
    intro e he
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hi).2
  have hsum : (∑ i, (C i).card) ≤ (crossing ends P).card := by
    rw [← Finset.card_biUnion hdis]
    exact Finset.card_le_card hsub
  have hi : ∀ i, (P.parts.card : ℤ) - 1 ≤ ((C i).card : ℤ) := by
    intro i
    have h := tree_crossing_card ends P (ht i)
    change P.parts.card ≤ (C i).card + 1 at h
    omega
  have hs := Finset.sum_le_sum (fun (i : Fin k) (_ : i ∈ Finset.univ) => hi i)
  have hsum' : (∑ i, ((C i).card : ℤ)) ≤ ((crossing ends P).card : ℤ) := by
    exact_mod_cast hsum
  change (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ ((crossing ends P).card : ℤ)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hs.trans hsum'

end NashWilliams61.TreePacking.NWFresh
end


section

open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Theorem 1** (Nash-Williams 1961, p. 445). A finite loopless multigraph `G` on a
non-empty vertex set has `k` edge-disjoint spanning trees if and only if
`|E_P(G)| ≥ k(|P| − 1)` for every partition `P` of `V(G)`. -/
theorem theorem_1 {V E : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype E]
    [DecidableEq E] (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k) :
    (∃ T : Fin k → Finset E, (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
        ∀ i, IsSpanningTree ends (T i)) ↔
      ∀ P : Finpartition (Finset.univ : Finset V),
        (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ ((crossing ends P).card : ℤ) := by
  constructor
  · rintro ⟨T, hd, ht⟩
    exact NWFresh.packing_admissible ends k T hd ht
  · intro ha
    exact NWFresh.admissible_hasKTrees ends hloop k hk ha

end NashWilliams61.TreePacking

end


theorem solution {V E : Type} [Fintype V] [DecidableEq V] [Nonempty V] [Fintype E]
    [DecidableEq E] (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k) :
    (∃ T : Fin k → Finset E, (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
        ∀ i, NashWilliams61.TreePacking.IsSpanningTree ends (T i)) ↔
      ∀ P : Finpartition (Finset.univ : Finset V),
        (k : ℤ) * ((P.parts.card : ℤ) - 1) ≤ ((NashWilliams61.TreePacking.crossing ends P).card : ℤ) := by
  exact NashWilliams61.TreePacking.theorem_1 ends hloop k hk
