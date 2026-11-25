-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed_of_ringKrullDim_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:33.135844+00:00
-- url     : https://prove2.me/submissions/4128a5c0-a97a-4b09-ae1f-7f435ff535e0

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularCurve
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_one
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_IsRegularLocalRing_isDomain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u
namespace GroundTheory.Arith.SchemeCoh
namespace IsRegularLocalRing
theorem _root_.solution {R : Type*}
    [CommRing R] [IsRegularLocalRing R] (h : ringKrullDim R ≤ 1) : IsIntegrallyClosed R :=
  have : IsDomain R := IsRegularLocalRing.isDomain
  have := IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_one h
  inferInstance
end IsRegularLocalRing
end GroundTheory.Arith.SchemeCoh
