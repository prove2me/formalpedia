-- Prove2me | solution 1 for GroundTheory.LocalField.range_cycNorm_ofMulDistribMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:14:23.528267+00:00
-- url     : https://prove2.me/submissions/18f56d95-5a91-42fe-9ba4-60137fca46c5

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_LocalField_toMul_cycNorm

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
namespace GroundTheory.LocalField
theorem _root_.solution :
    (cycNorm (Representation.ofMulDistribMulAction G M)).range =
      (tateNorm G M).range.toAddSubgroup := by
  ext y
  rw [AddMonoidHom.mem_range, Additive.mem_toAddSubgroup, MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.toMul, (toMul_cycNorm x).symm⟩
  · rintro ⟨x, hx⟩
    refine ⟨Additive.ofMul x, Additive.toMul.injective ?_⟩
    rw [toMul_cycNorm]
    exact hx
end GroundTheory.LocalField
