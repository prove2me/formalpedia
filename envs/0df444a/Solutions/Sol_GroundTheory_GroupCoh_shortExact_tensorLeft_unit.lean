-- Prove2me | solution 1 for GroundTheory.GroupCoh.shortExact_tensorLeft_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:56:55.800805+00:00
-- url     : https://prove2.me/submissions/1241894a-891e-4e26-8a4b-abf73f16eb7e

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_CupTate
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateCupUnit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (E : ShortComplex (Rep.{u} k G))
variable {E}
namespace GroundTheory.GroupCoh
theorem _root_.solution (hE : E.ShortExact) :
    (E.map (tensorLeft (𝟙_ (Rep.{u} k G)))).ShortExact :=
  ShortComplex.shortExact_of_iso (leftUnitorSCIso E).symm hE
end GroundTheory.GroupCoh
