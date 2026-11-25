-- Prove2me | solution 2 for GroundTheory.Global.orbitPoint_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:26:30.012653+00:00
-- url     : https://prove2.me/submissions/87044a99-6d8c-45ae-99e7-3b77e96e63cc

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Cyclic
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_Permutation
import Theorems.Thm_GroundTheory_Global_mk_orbitPoint

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
theorem _root_.solution (x : X) : orbitPoint G x ∈ orbit G x :=
  orbitRel_apply.1 (Quotient.exact (mk_orbitPoint x))
end GroundTheory.Global
