-- Prove2me | solution 1 for GroundTheory.LocalField.Abstract.TateModel.natCard_tateZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:10:46.625664+00:00
-- url     : https://prove2.me/submissions/7a1f332f-a60d-4e57-878b-24f212db2ba3

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
variable [(L.subgroupOf K).Normal]
include T
namespace GroundTheory.LocalField.Abstract.TateModel
theorem _root_.solution [Fintype Γ] [(L.subgroupOf K).FiniteIndex] :
    Nat.card (tateZero A K L) = Nat.card (TateZero Γ M) :=
  Nat.card_congr T.tateZeroEquiv.toEquiv
end GroundTheory.LocalField.Abstract.TateModel
