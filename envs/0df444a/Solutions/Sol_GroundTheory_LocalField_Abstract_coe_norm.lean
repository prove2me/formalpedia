-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.coe_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:05.170554+00:00
-- url     : https://prove2.me/submissions/be4b8524-cec6-4163-8ca6-3c6a1101d641

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
variable (K L : Subgroup G)
variable {A K L}
variable (A K L)
variable [(L.subgroupOf K).FiniteIndex]
variable {A K L}
namespace GroundTheory.LocalField.Abstract
theorem _root_.solution (a : fixedModule A L) :
    (norm A K L a : A) = ∏ᶠ q, cosetSMul A K L a q :=
  rfl
end GroundTheory.LocalField.Abstract
