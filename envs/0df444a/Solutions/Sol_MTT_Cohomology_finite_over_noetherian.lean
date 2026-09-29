-- Prove2me | solution 1 for MTT.Cohomology.finite_over_noetherian
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T17:17:02.554656+00:00
-- url     : https://prove2.me/submissions/6195e60b-a132-4d90-889d-5bf1fc3a64c7

import Definitions.Def_MTT_Cohomology
import Theorems.Thm_MTT_Cohomology_manin_coordinates

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem solution {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] [IsNoetherianRing R] :
    Module.Finite R (Hc N n R) := by
  obtain ⟨m, T, hT⟩ := MTT.Cohomology.manin_coordinates (N := N) (n := n) hN R
  exact Module.Finite.of_injective T hT
