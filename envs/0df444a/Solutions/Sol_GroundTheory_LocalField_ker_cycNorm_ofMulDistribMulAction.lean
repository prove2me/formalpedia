-- Prove2me | solution 1 for GroundTheory.LocalField.ker_cycNorm_ofMulDistribMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:20.394017+00:00
-- url     : https://prove2.me/submissions/5945037c-e9f9-4948-8263-54a5ef6cc8ab

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
    (cycNorm (Representation.ofMulDistribMulAction G M)).ker = (tateNorm G M).ker.toAddSubgroup := by
  ext x
  rw [AddMonoidHom.mem_ker, Additive.mem_toAddSubgroup, MonoidHom.mem_ker, ← toMul_cycNorm]
  exact ⟨fun h => by rw [h]; rfl, fun h => by rw [← toMul_zero] at h; exact Additive.toMul.injective h⟩
end GroundTheory.LocalField
