-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isIntegrallyClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:25:44.522483+00:00
-- url     : https://prove2.me/submissions/9d5fe4a1-18b7-45ec-b78d-aeb05a5b4455

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFDLocalization
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularUFD

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
open IsLocalRing Ideal Module
universe u
namespace GroundTheory.Arith.SchemeCoh
namespace IsRegularLocalRing
theorem _root_.solution (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsIntegrallyClosed R :=
  inferInstance
end IsRegularLocalRing
end GroundTheory.Arith.SchemeCoh
