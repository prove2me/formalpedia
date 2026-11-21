-- Prove2me | solution 1 for MasulloGRH.bidual_nuclear_of_frechet_strong_dual_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:19:52.533208+00:00
-- url     : https://prove2.me/submissions/18d6e32d-5ceb-4f6d-9885-c83d4ea6dec5

import Definitions.Def_MasulloGRH_LocallyConvex
import Theorems.Thm_MasulloGRH_strongDual_frechet_isCompleteTVS
import Theorems.Thm_MasulloGRH_strongDual_frechet_isDF
import Theorems.Thm_MasulloGRH_strongDual_nuclear_of_complete_nuclear_DF

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear (StrongDual ℂ E)) :
    IsNuclear (StrongDual ℂ (StrongDual ℂ E)) := by
  obtain ⟨hB, hDF⟩ := strongDual_frechet_isDF E hE
  exact strongDual_nuclear_of_complete_nuclear_DF (StrongDual ℂ E)
    (strongDual_frechet_isCompleteTVS E hE) hN hB hDF
