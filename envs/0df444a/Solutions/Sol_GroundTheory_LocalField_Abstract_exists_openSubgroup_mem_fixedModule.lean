-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.exists_openSubgroup_mem_fixedModule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:34.397038+00:00
-- url     : https://prove2.me/submissions/7f414ff6-b888-49b1-a50d-21fac8562c4e

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
variable {G : Type*} [Group G] [TopologicalSpace G] {A : Type*} [CommGroup A]
  [MulDistribMulAction G A]
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution [IsDiscreteModule G A] (a : A) :
    ∃ U : OpenSubgroup G, a ∈ fixedModule A (U : Subgroup G) :=
  ⟨⟨MulAction.stabilizer G a, IsDiscreteModule.isOpen_stabilizer a⟩, fun _ hg => hg⟩
end GroundTheory.LocalField.Abstract
