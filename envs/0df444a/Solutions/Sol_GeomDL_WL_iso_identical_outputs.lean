-- Prove2me | solution 1 for GeomDL.WL.iso_identical_outputs
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:53:07.222814+00:00
-- url     : https://prove2.me/submissions/832b4de4-f3e3-4f22-9478-0124f3b3a5ce

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

open GeomDL.WL OAI.WLIdentification

theorem nbhd_map_aux (G G' : Graph)
    (e : Fin G.order ≃ Fin G'.order) (he : ∀ u v, G.edge u v = G'.edge (e u) (e v))
    (u : Fin G.order) : (nbhd G u).map e.toEmbedding = nbhd G' (e u) := by
  ext w
  simp only [nbhd, Finset.mem_map_equiv, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [he, Equiv.apply_symm_apply]

theorem solution {F M A Y : Type*} (N : GNN F M A) (G G' : Graph)
    (e : Fin G.order ≃ Fin G'.order) (he : ∀ u v, G.edge u v = G'.edge (e u) (e v)) :
    (∀ t u, N.features G t u = N.features G' t (e u)) ∧
      ∀ (readout : Multiset F → Y) (T : ℕ), N.output readout G T = N.output readout G' T := by
  have hf : ∀ t u, N.features G t u = N.features G' t (e u) := by
    intro t
    induction t with
    | zero => intro u; rfl
    | succ t ih =>
      intro u
      simp only [GNN.features, MPLayer.apply]
      rw [← nbhd_map_aux G G' e he u, Finset.map_val, Multiset.map_map, ih u]
      congr 2
      apply Multiset.map_congr rfl
      intro v _
      simp [ih v]
  refine ⟨hf, fun readout T => ?_⟩
  simp only [GNN.output]
  congr 1
  rw [← Finset.map_univ_equiv e, Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro v _
  simp [hf T v]
