-- Prove2me | solution 1 for KernelRamsey.ram2_symm
-- status  : ACCEPTED   (prove)
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:47:03.904907+00:00
-- url     : https://prove2.me/submissions/d9150d77-56d1-4b3f-89b4-8485e632a825

import Mathlib
import Definitions.Def_KernelRamsey_Ram
open KernelRamsey Finset

theorem solution {s t m : Nat} (h : Ram2 s t m) : Ram2 t s m := by
  intro V G A hA
  rcases h Gᶜ A hA with ⟨T, hT, h1⟩ | ⟨I, hI, h2⟩
  · exact Or.inr ⟨T, hT, h1⟩
  · rw [compl_compl] at h2
    exact Or.inl ⟨I, hI, h2⟩
