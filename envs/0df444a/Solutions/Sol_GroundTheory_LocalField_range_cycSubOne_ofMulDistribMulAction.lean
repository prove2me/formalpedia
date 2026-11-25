-- Prove2me | solution 1 for GroundTheory.LocalField.range_cycSubOne_ofMulDistribMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:17:25.32399+00:00
-- url     : https://prove2.me/submissions/9d90db34-0b73-4178-b726-d9e1000409cd

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_Global_range_cycSubOne_eq_closure


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
omit [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).range =
      (augmentation G M).toAddSubgroup := by
  rw [range_cycSubOne_eq_closure _ hσ, augmentation, Subgroup.toAddSubgroup_closure]
  congr 1
end GroundTheory.LocalField
