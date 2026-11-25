-- Prove2me | solution 1 for GroundTheory.GroupCoh.iCocycles_cyclesMap_revHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:37.129792+00:00
-- url     : https://prove2.me/submissions/3f08cb68-b579-4cab-a68f-107b1f9321a6

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_CochainReverse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
universe u
open CategoryTheory Limits groupCohomology
open GroundTheory GroundTheory.GroupCoh
variable {k G : Type u} [CommRing k] [Group G]
variable {A : Rep k G} {n : ℕ}
namespace GroundTheory.GroupCoh
theorem _root_.solution (z : cocycles A n) :
    iCocycles A n (HomologicalComplex.cyclesMap (revHom A) n z) = revCochain n (iCocycles A n z) :=
  congr(($(HomologicalComplex.cyclesMap_i (revHom A) n)).hom z)
end GroundTheory.GroupCoh
