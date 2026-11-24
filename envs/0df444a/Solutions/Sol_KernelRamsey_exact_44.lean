-- Prove2me | solution 1 for KernelRamsey.exact_44
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T18:49:26.605476+00:00
-- url     : https://prove2.me/submissions/c90687c1-5cba-42a3-8e6f-51c9c441b745

import Mathlib
import Theorems.Thm_KernelRamsey_bound_r44
import Theorems.Thm_KernelRamsey_no_avoid_44
open KernelRamsey

theorem solution :
    (∃ G : SimpleGraph (Fin 17), G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4) ∧
    ∀ G : SimpleGraph (Fin 18), ¬ (G.CliqueFree 4 ∧ Gᶜ.CliqueFree 4) := ⟨bound_r44, no_avoid_44⟩
