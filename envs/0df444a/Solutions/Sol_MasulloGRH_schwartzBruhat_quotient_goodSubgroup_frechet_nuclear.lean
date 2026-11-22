-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_quotient_goodSubgroup_frechet_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:34:20.462177+00:00
-- url     : https://prove2.me/submissions/efe569ce-6570-4773-b523-4f65a79a0d5b

import Theorems.Thm_MasulloGRH_quotient_goodSubgroup_exists_elemPresentation
import Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv_univ
import Theorems.Thm_MasulloGRH_schwartzBruhat_equiv_elem_of_minimal_goodSubgroup
import Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel

set_option autoImplicit false

universe u

open MasulloGRH

theorem solution
    (G : Type u) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (k : Subgroup G) (hk : IsGoodSubgroup k) [T2Space (G ⧸ k)] :
    IsFrechet (SchwartzBruhat (G ⧸ k)) ∧ IsNuclear (SchwartzBruhat (G ⧸ k)) := by
  obtain ⟨a, n, r, s, d, π₀, hs, hπ⟩ := quotient_goodSubgroup_exists_elemPresentation G m hm k hk
  obtain ⟨⟨e⟩, hF⟩ := schwartzBruhat_equiv_elem_of_minimal_goodSubgroup (G ⧸ k) ⊥ a n r s d π₀ hs hπ
    (fun _ _ => bot_le)
  exact ⟨hF, nuclear_of_continuousLinearEquiv_univ _ _ e.symm
    (elemSchwartz_frechet_nuclear_montel a n r s d hπ.1).2.1⟩

