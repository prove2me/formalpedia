-- Prove2me | solution 1 for GroundTheory.LocalField.ker_cycSubOne_ofMulDistribMulAction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:14:21.668567+00:00
-- url     : https://prove2.me/submissions/288547ad-8eea-41c0-aca8-e07f8ff14140

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HerbrandCyclic
import Theorems.Thm_GroundTheory_Global_mem_ker_cycSubOne_iff
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_mem_invariants
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F



set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open GroundTheory.GroupCoh GroundTheory.Global
variable {G M : Type*} [Group G] [Fintype G] [CommGroup M] [MulDistribMulAction G M]
variable {σ : G}
omit [Fintype G]
namespace GroundTheory.LocalField
theorem _root_.solution (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    (cycSubOne (Representation.ofMulDistribMulAction G M) σ).ker =
      (invariants G M).toAddSubgroup := by
  ext x
  rw [mem_ker_cycSubOne_iff _ hσ, Additive.mem_toAddSubgroup, mem_invariants]
  simp only [Representation.ofMulDistribMulAction_apply_apply]
  exact ⟨fun h g => congrArg Additive.toMul (h g), fun h g => by rw [h g]; rfl⟩
end GroundTheory.LocalField
