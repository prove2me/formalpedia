-- Prove2me | solution 1 for GroundTheory.GroupCoh.coeffOneProj_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:36.702448+00:00
-- url     : https://prove2.me/submissions/87f036e0-7936-4a83-8212-ad2730d4fa93

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep MonoidalCategory
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
omit [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution (x : MonoidAlgebra k G) :
    coeffOneProj x = MonoidAlgebra.single 1 (x.coeff 1) := rfl
end GroundTheory.GroupCoh
