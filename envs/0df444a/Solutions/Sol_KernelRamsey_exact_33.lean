-- Prove2me | solution 1 for KernelRamsey.exact_33
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:51:15.809274+00:00
-- url     : https://prove2.me/submissions/d8e9d277-31ef-487a-85fb-7c0d70d02743

import Mathlib
import Theorems.Thm_KernelRamsey_bound_r33
import Theorems.Thm_KernelRamsey_no_avoid_33
open KernelRamsey

theorem solution :
    (∃ G : SimpleGraph (Fin 5), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3) ∧
    ∀ G : SimpleGraph (Fin 6), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3) := ⟨bound_r33, no_avoid_33⟩
