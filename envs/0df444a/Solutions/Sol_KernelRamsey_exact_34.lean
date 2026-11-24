-- Prove2me | solution 1 for KernelRamsey.exact_34
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:02:28.24164+00:00
-- url     : https://prove2.me/submissions/9bfed16a-39fe-4a7f-84b9-1f922c203283

import Mathlib
import Theorems.Thm_KernelRamsey_bound_r34
import Theorems.Thm_KernelRamsey_no_avoid_34
open KernelRamsey

theorem solution :
    (∃ G : SimpleGraph (Fin 8), G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4) ∧
    ∀ G : SimpleGraph (Fin 9), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 4) := ⟨bound_r34, no_avoid_34⟩
