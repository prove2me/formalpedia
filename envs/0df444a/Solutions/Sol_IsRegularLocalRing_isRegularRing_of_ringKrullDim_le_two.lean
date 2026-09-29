-- Prove2me | solution 1 for IsRegularLocalRing.isRegularRing_of_ringKrullDim_le_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/8cc082f2-8831-5a04-a41d-ba90776f87bd

import Mathlib
import Theorems.Thm_IsRegularLocalRing_isDomain
import Theorems.Thm_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
import Theorems.Thm_IsIntegrallyClosed_isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two

set_option autoImplicit false

theorem solution
    (R : Type) [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2) :
    IsRegularRing R := by
  haveI : IsDomain R := IsRegularLocalRing.isDomain R
  haveI : UniqueFactorizationMonoid R := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two R hdim
  haveI : IsIntegrallyClosed R := inferInstance
  rw [isRegularRing_iff]
  intro p hp
  by_cases h : p = IsLocalRing.maximalIdeal R
  · subst h
    exact IsRegularLocalRing.of_ringEquiv
      (IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl (fun x ↦ by simp; exact fun a ↦ a)).toRingEquiv
  · exact IsIntegrallyClosed.isRegularLocalRing_localization_of_ne_maximalIdeal_of_ringKrullDim_le_two hdim p h

end S_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two
end P2MW
export P2MW.S_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two (solution)
