-- Prove2me | solution 1 for GeomDL.WL.gnn_le_wl
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:01:27.32557+00:00
-- url     : https://prove2.me/submissions/9ad07749-f472-46e6-91a5-5405afc8e0fe

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

open GeomDL.WL OAI.WLIdentification

/-- The feature a GNN assigns to a node, read off from the node's WL colour. -/
def gnnColorFeature {F M A : Type*} (N : GNN F M A) : (t : ℕ) → NeighborColor t → F
  | 0 => fun _ => N.init
  | t + 1 => fun x =>
      let c : NeighborColor t × Multiset (NeighborColor t) := x
      (N.layer t).φ (gnnColorFeature N t c.1)
        ((N.layer t).agg (c.2.map (fun d =>
          (N.layer t).ψ (gnnColorFeature N t c.1) (gnnColorFeature N t d))))

theorem gnnColorFeature_spec {F M A : Type*} (N : GNN F M A) (G : Graph) :
    ∀ (t : ℕ) (u : Fin G.order),
      N.features G t u = gnnColorFeature N t (neighborColor G t u) := by
  intro t
  induction t with
  | zero => intro u; rfl
  | succ t ih =>
    intro u
    show (N.layer t).φ (N.features G t u)
        ((N.layer t).agg ((nbhd G u).val.map
          (fun v => (N.layer t).ψ (N.features G t u) (N.features G t v)))) =
      (N.layer t).φ (gnnColorFeature N t (neighborColor G t u))
        ((N.layer t).agg ((((Finset.univ.filter (fun w => G.edge u w = true)).val.map
          (neighborColor G t))).map (fun d =>
          (N.layer t).ψ (gnnColorFeature N t (neighborColor G t u)) (gnnColorFeature N t d))))
    rw [Multiset.map_map, ih u]
    congr 3
    funext v
    simp [ih v]

theorem solution {F M A Y : Type*} (N : GNN F M A) (readout : Multiset F → Y) (T : ℕ)
    (G G' : Graph) :
    (∀ t ≤ T, ∀ u v, neighborColor G t u = neighborColor G' t v →
        N.features G t u = N.features G' t v) ∧
      (neighborHistogram G T = neighborHistogram G' T →
        N.output readout G T = N.output readout G' T) := by
  constructor
  · intro t _ u v h
    rw [gnnColorFeature_spec N G, gnnColorFeature_spec N G', h]
  · intro h
    have hG : Finset.univ.val.map (N.features G T) =
        (neighborHistogram G T).map (gnnColorFeature N T) := by
      rw [neighborHistogram, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro u _
      exact gnnColorFeature_spec N G T u
    have hG' : Finset.univ.val.map (N.features G' T) =
        (neighborHistogram G' T).map (gnnColorFeature N T) := by
      rw [neighborHistogram, Multiset.map_map]
      apply Multiset.map_congr rfl
      intro u _
      exact gnnColorFeature_spec N G' T u
    simp only [GNN.output]
    rw [hG, hG', h]
