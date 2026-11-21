-- Prove2me | solution 1 for MasulloGRH.nuclear_of_frechet_bidual_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T23:08:21.861387+00:00
-- url     : https://prove2.me/submissions/03aa88a6-d555-4e6c-89d6-59125f5e2334

import Theorems.Thm_MasulloGRH_nuclear_subspace
import Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv
import Theorems.Thm_MasulloGRH_frechet_equiv_subspace_bidual

set_option autoImplicit false

open MasulloGRH

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (hN : IsNuclear (StrongDual ℂ (StrongDual ℂ E))) :
    IsNuclear E := by
  obtain ⟨V, ⟨e⟩⟩ := frechet_equiv_subspace_bidual E hE
  letI : AddCommGroup V :=
    @Submodule.addCommGroup ℂ (StrongDual ℂ (StrongDual ℂ E)) _ ContinuousLinearMap.addCommGroup _ V
  exact nuclear_of_continuousLinearEquiv E V e (nuclear_subspace _ hN V)
