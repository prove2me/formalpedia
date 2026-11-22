-- Prove2me | solution 2 for MasulloGRH.schwartzBruhat_quotient_goodSubgroup_frechet_nuclear
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T18:42:03.43504+00:00
-- url     : https://prove2.me/submissions/07beefdc-1a0d-42b0-9c74-d2bde25555be

import Theorems.Thm_MasulloGRH_quotient_goodSubgroup_exists_elemPresentation
import Theorems.Thm_MasulloGRH_nuclear_of_continuousLinearEquiv_elemSchwartz
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
  exact ⟨hF, nuclear_of_continuousLinearEquiv_elemSchwartz _ a n r s d hπ.1 e.symm⟩

