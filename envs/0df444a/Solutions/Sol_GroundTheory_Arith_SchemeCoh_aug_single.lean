-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.aug_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:43:47.789921+00:00
-- url     : https://prove2.me/submissions/f9b9f08c-0ae0-46c4-ae2b-baf19f2069af

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains

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
open CategoryTheory
universe w
variable {ι : Type w}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (j : Fin 1 → ι) (z : ℤ) : aug (Finsupp.single j z) = z :=
  Finsupp.liftAddHom_apply_single _ _ _
end GroundTheory.Arith.SchemeCoh
