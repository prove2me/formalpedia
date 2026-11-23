-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.mem_fixedModule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:32.499251+00:00
-- url     : https://prove2.me/submissions/4ea0d9e4-629c-4578-8695-23220401b3aa

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
theorem _root_.solution {H : Subgroup G} {a : A} :
    a ∈ fixedModule A H ↔ ∀ g ∈ H, g • a = a :=
  Iff.rfl
end GroundTheory.LocalField.Abstract
