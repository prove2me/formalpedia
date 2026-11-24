-- Prove2me | solution 1 for KernelRamsey.exact_35
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:18:49.682836+00:00
-- url     : https://prove2.me/submissions/bb536cb2-3428-495c-b144-b9c89ba8601f

import Mathlib
import Theorems.Thm_KernelRamsey_bound_r35
import Theorems.Thm_KernelRamsey_no_avoid_35
open KernelRamsey

theorem solution :
    (∃ G : SimpleGraph (Fin 13), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5) ∧
    ∀ G : SimpleGraph (Fin 14), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 5) := ⟨bound_r35, no_avoid_35⟩
