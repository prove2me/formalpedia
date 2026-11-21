-- Prove2me | solution 1 for MasulloGRH.strong_dual_nuclear_of_nuclear_frechet
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:00:40.208804+00:00
-- url     : https://prove2.me/submissions/b886cad4-b717-4c7f-b6e3-ea8c54b1f593

import Theorems.Thm_MasulloGRH_nuclear_of_quasinuclear_domination
import Theorems.Thm_MasulloGRH_strongDual_isHLCS
import Theorems.Thm_MasulloGRH_strongDual_quasinuclear_domination

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear E) :
    IsNuclear (StrongDual ℂ E) :=
  nuclear_of_quasinuclear_domination (StrongDual ℂ E)
    (strongDual_isHLCS E ⟨hE.1, hE.2.1.1⟩)
    (fun p hp => strongDual_quasinuclear_domination E hE hN p hp)
