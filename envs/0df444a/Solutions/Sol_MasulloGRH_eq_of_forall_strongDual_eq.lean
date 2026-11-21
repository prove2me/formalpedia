-- Prove2me | solution 1 for MasulloGRH.eq_of_forall_strongDual_eq
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-21T00:28:13.451175+00:00
-- url     : https://prove2.me/submissions/89594028-dbea-463d-8a19-8b97fd8f775b

import Definitions.Def_MasulloGRH_LocallyConvex

set_option autoImplicit false

open MasulloGRH

theorem solution (G : Type*) [AddCommGroup G] [Module ℂ G]
    [TopologicalSpace G] (hL : IsHLCS G) (x z : G)
    (h : ∀ f : StrongDual ℂ G, f x = f z) : x = z := by
  obtain ⟨⟨ι, _, p, hp⟩, hT2⟩ := hL
  have := hp.topologicalAddGroup
  have := hp.continuousSMul
  have := hp.toLocallyConvexSpace (E := G)
  by_contra hxz
  obtain ⟨f, hf⟩ := RCLike.geometric_hahn_banach_point_point (𝕜 := ℂ) hxz
  rw [h f] at hf
  exact lt_irrefl _ hf

