-- Prove2me | solution 1 for GeomDL.WL.injective_phi_one_wl_step
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:52:45.698955+00:00
-- url     : https://prove2.me/submissions/a2c521ff-e6e4-4baf-92b0-7fa9ce5dada9

import Mathlib
import Definitions.Def_WLIdentification
import Definitions.Def_GeomDL_WL_Defs

open GeomDL.WL OAI.WLIdentification

theorem solution {F : Type*} (φ : F → Multiset F → F)
    (hφ : Function.Injective2 φ) (G G' : Graph) (s : ℕ)
    (h : Fin G.order → F) (h' : Fin G'.order → F)
    (hs : ∀ u v, h u = h' v ↔ neighborColor G s u = neighborColor G' s v) :
    ∀ u v, localLayer φ G h u = localLayer φ G' h' v ↔
      neighborColor G (s + 1) u = neighborColor G' (s + 1) v := by
  intro u v
  have hmul : ∀ (A : Multiset (Fin G.order)) (B : Multiset (Fin G'.order)),
      A.map h = B.map h' ↔ A.map (neighborColor G s) = B.map (neighborColor G' s) := by
    intro A B
    rw [← Multiset.rel_eq, ← Multiset.rel_eq, Multiset.rel_map, Multiset.rel_map]
    constructor
    · exact fun H => H.mono (fun a _ b _ hab => (hs a b).mp hab)
    · exact fun H => H.mono (fun a _ b _ hab => (hs a b).mpr hab)
  show φ (h u) ((nbhd G u).val.map h) = φ (h' v) ((nbhd G' v).val.map h') ↔
    ((neighborColor G s u, (nbhd G u).val.map (neighborColor G s)) :
      NeighborColor s × Multiset (NeighborColor s)) =
      (neighborColor G' s v, (nbhd G' v).val.map (neighborColor G' s))
  rw [Prod.mk.injEq]
  constructor
  · intro H
    obtain ⟨h1, h2⟩ := hφ H
    exact ⟨(hs u v).mp h1, (hmul _ _).mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [(hs u v).mpr h1, (hmul _ _).mpr h2]
