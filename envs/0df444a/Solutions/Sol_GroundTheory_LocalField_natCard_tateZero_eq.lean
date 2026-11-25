-- Prove2me | solution 1 for GroundTheory.LocalField.natCard_tateZero_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:25:40.618566+00:00
-- url     : https://prove2.me/submissions/0b5f1112-e846-4f96-89f9-aa53870ce9a4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_LocalField_range_cycNorm_ofMulDistribMulAction
import Theorems.Thm_GroundTheory_LocalField_ker_cycSubOne_ofMulDistribMulAction

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
    Nat.card (TateZero G M) =
      Nat.card (CycTateZero (Representation.ofMulDistribMulAction G M) σ) := by
  change (tateNorm G M).range.relIndex (invariants G M) =
    (cycNorm (Representation.ofMulDistribMulAction G M)).range.relIndex
      (cycSubOne (Representation.ofMulDistribMulAction G M) σ).ker
  rw [ker_cycSubOne_ofMulDistribMulAction hσ, range_cycNorm_ofMulDistribMulAction,
    Subgroup.relIndex_toAddSubgroup]
end GroundTheory.LocalField
