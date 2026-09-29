-- Prove2me | solution 1 for IsRegularLocalRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/94790848-6005-5646-995b-2b48ce334e7e

import Mathlib
import Theorems.Thm_IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    (h : ringKrullDim R = 1) : IsRegularLocalRing R := by
  haveI := IsDiscreteValuationRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one R h
  infer_instance

end S_IsRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
end P2MW
export P2MW.S_IsRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one (solution)
