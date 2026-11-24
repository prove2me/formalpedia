-- Prove2me | solution 1 for KernelRamsey.no_avoid_33
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T17:36:08.205564+00:00
-- url     : https://prove2.me/submissions/a9539c99-4f6f-471d-9efd-fdb8462bde19

import Mathlib
import Definitions.Def_KernelRamsey_Ram
import Theorems.Thm_KernelRamsey_ram_33
open KernelRamsey Finset

theorem solution : ∀ G : SimpleGraph (Fin 6), ¬ (G.CliqueFree 3 ∧ Gᶜ.CliqueFree 3) := by
  intro G ⟨h1, h2⟩
  rcases ram_33 G (Finset.univ : Finset (Fin 6)) (by simp) with ⟨T, _, hT⟩ | ⟨I, _, hI⟩
  · exact h1 T hT
  · exact h2 I hI
