-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.fixedModule_anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:31:19.901155+00:00
-- url     : https://prove2.me/submissions/cca6d1e3-acd7-409a-8c65-da2791498a7b

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ProfiniteInteger
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.Abstract
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
variable {A}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution {H H' : Subgroup G} (h : H ≤ H') : fixedModule A H' ≤ fixedModule A H :=
  fun _ ha g hg => ha g (h hg)
end GroundTheory.LocalField.Abstract
