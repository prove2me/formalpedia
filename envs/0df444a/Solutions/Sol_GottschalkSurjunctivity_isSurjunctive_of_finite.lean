-- Prove2me | solution 1 for GottschalkSurjunctivity.isSurjunctive_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:03:36.864872+00:00
-- url     : https://prove2.me/submissions/1a792360-4172-43ba-b455-3f4297e18263

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs
open GottschalkSurjunctivity

theorem solution (G : Type) [Group G] [Finite G] : IsSurjunctive G := by
  intro A _ _ _ _ τ _ _ hτ
  exact Finite.surjective_of_injective hτ
