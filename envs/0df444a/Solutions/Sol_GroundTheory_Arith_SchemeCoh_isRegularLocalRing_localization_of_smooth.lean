-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isRegularLocalRing_localization_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:13:28.559077+00:00
-- url     : https://prove2.me/submissions/dd615542-edcb-478b-8764-1ce5a8ea8285

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularRing_of_smooth

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
theorem _root_.solution (k A : Type*) [CommRing k] [IsRegularRing k]
    [CommRing A] [Algebra k A] [Algebra.Smooth k A] (q : Ideal A) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  have := isRegularRing_of_smooth k A
  inferInstance
end GroundTheory.Arith.SchemeCoh
