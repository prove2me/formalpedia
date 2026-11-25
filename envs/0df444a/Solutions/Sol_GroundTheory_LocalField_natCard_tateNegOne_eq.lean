-- Prove2me | solution 1 for GroundTheory.LocalField.natCard_tateNegOne_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:28:08.405848+00:00
-- url     : https://prove2.me/submissions/8c91ba45-c176-4acb-afb3-3600cf9b3ffc

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_LocalField_ker_cycNorm_ofMulDistribMulAction
import Theorems.Thm_GroundTheory_LocalField_range_cycSubOne_ofMulDistribMulAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
namespace GroundTheory.LocalField
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (TateNegOne G M) =
      Nat.card (CycTateNegOne (Representation.ofMulDistribMulAction G M) σ) := by
  change (augmentation G M).relIndex (tateNorm G M).ker =
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range.relIndex
      (cycNorm (Representation.ofMulDistribMulAction G M)).ker
  rw [range_cycSubOne_ofMulDistribMulAction hσ, ker_cycNorm_ofMulDistribMulAction,
    Subgroup.relIndex_toAddSubgroup]
end GroundTheory.LocalField
