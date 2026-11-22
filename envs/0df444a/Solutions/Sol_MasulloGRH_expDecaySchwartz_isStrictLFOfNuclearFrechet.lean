-- Prove2me | solution 1 for MasulloGRH.expDecaySchwartz_isStrictLFOfNuclearFrechet
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:57:07.646688+00:00
-- url     : https://prove2.me/submissions/1baeef84-ddc2-42f7-827e-7f63350bb930

import Theorems.Thm_MasulloGRH_isStrictLFOfNuclearFrechet_of_retract_stages
import Theorems.Thm_MasulloGRH_expDecaySchwartz_exists_stages

set_option autoImplicit false

open MasulloGRH in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] (m : G → ℝ) (hm : IsRposModule m)
    (I : Set ℝ) (hI : I.OrdConnected) (hne : I.Nonempty) :
    IsStrictLFOfNuclearFrechet (ExpDecaySchwartz G m I) := by
  obtain ⟨F, i1, i2, i3, J, P, hF, hJ, hP, hPJ, hmono, hexh, htop⟩ :=
    expDecaySchwartz_exists_stages G m hm I hI hne
  exact isStrictLFOfNuclearFrechet_of_retract_stages _ F hF J P hJ hP hPJ hmono hexh htop
