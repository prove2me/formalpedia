-- Prove2me | solution 1 for GlobalTheory.RelIndexOfMap.relIndex_eq_of_map
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:20:39.221866+00:00
-- url     : https://prove2.me/submissions/664c131c-4025-442d-aa64-c562aef28323

import Mathlib


theorem solution {X P : Type} [Group X] [Group P] (φ : X →* P) (A B : Subgroup X)
    (U V : Subgroup P) (hA : A.map φ = U) (hB : ∀ a ∈ A, a ∈ B ↔ φ a ∈ V) :
    B.relIndex A = V.relIndex U := by
  subst U; rw [← Subgroup.relIndex_comap]
  unfold Subgroup.relIndex; congr 1; ext x; exact hB x x.2
