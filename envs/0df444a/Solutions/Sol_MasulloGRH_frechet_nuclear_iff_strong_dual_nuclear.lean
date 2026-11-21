-- Prove2me | solution 1 for MasulloGRH.frechet_nuclear_iff_strong_dual_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T22:35:38.696859+00:00
-- url     : https://prove2.me/submissions/56b8dde3-2e1f-46af-9411-a9b7a53f9eac

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strong_dual_nuclear_of_nuclear_frechet
import Theorems.Thm_MasulloGRH_bidual_nuclear_of_frechet_strong_dual_nuclear
import Theorems.Thm_MasulloGRH_nuclear_of_frechet_bidual_nuclear

set_option autoImplicit false

open MasulloGRH in
theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) :
    IsNuclear E ↔ IsNuclear (StrongDual ℂ E) :=
  ⟨strong_dual_nuclear_of_nuclear_frechet E hE,
   fun h => nuclear_of_frechet_bidual_nuclear E hE
     (bidual_nuclear_of_frechet_strong_dual_nuclear E hE h)⟩
