-- Prove2me | solution 1 for GeomDL.Blueprint.pointwise_comp_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T19:36:37.04879+00:00
-- url     : https://prove2.me/submissions/ed68d2f8-ac3a-40a5-ac2a-36f8f56288da

import Mathlib
import Definitions.Def_GeomDL_Blueprint_Defs

open GeomDL.Blueprint

theorem solution {G Ω C C' C'' : Type*} [Group G] [MulAction G Ω]
    (B : (Ω → C) → (Ω → C')) (σ : C' → C'') (hB : IsEquivariant (G := G) B) :
    IsEquivariant (G := G) (pointwise (Ω := Ω) σ ∘ B) := by
  intro g x
  simp only [Function.comp, hB g x]
  rfl
