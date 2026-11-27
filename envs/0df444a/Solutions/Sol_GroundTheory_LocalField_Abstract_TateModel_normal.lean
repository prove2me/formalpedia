-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.TateModel.normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:26.539022+00:00
-- url     : https://prove2.me/submissions/93f22d31-efe1-40c4-b2fd-1e11a7de97f6

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_AbstractLocalReciprocity_ExistsOpenSubgroupMemFixedModule
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_LocalAxiomTransport
import Theorems.Thm_GroundTheory_LocalField_mem_invariants


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
open GroundTheory.LocalField (tateNorm invariants mem_invariants TateZero TateNegOne)
variable {G : Type*} [Group G] (A : Type*) [CommGroup A] [MulDistribMulAction G A]
  (K L : Subgroup G) (Γ : Type*) [Group Γ] (M : Type*) [CommGroup M] [MulDistribMulAction Γ M]
open GroundTheory.LocalField.Abstract.TateModel
variable {A K L Γ M} (T : TateModel A K L Γ M)
include T
namespace GroundTheory.LocalField.Abstract.TateModel
theorem _root_.solution : (L.subgroupOf K).Normal :=
  T.ker_hom ▸ T.hom.normal_ker
end GroundTheory.LocalField.Abstract.TateModel
