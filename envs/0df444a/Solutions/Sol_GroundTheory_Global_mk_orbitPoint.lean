-- Prove2me | solution 1 for GroundTheory.Global.mk_orbitPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:09:50.371771+00:00
-- url     : https://prove2.me/submissions/5e873097-7513-41d5-a712-53be0c7b06ac

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh MulAction
variable (G : Type*) {X : Type*} [Group G] [MulAction G X]
variable {G}
namespace GroundTheory.Global
theorem _root_.solution (x : X) :
    Quotient.mk (orbitRel G X) (orbitPoint G x) = Quotient.mk (orbitRel G X) x :=
  Quotient.out_eq _
end GroundTheory.Global
