-- Prove2me | solution 2 for GroundTheory.Global.orbitPoint_orbitPoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:34:23.45496+00:00
-- url     : https://prove2.me/submissions/370753bc-e3ca-416a-b448-a125b3374d5a

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_orbitPoint_mem
import Theorems.Thm_GroundTheory_Global_orbitPoint_eq_of_mem

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
theorem _root_.solution (x : X) : orbitPoint G (orbitPoint G x) = orbitPoint G x :=
  orbitPoint_eq_of_mem (orbitPoint_mem x)
end GroundTheory.Global
