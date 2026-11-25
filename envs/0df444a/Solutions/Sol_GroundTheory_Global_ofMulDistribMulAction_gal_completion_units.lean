-- Prove2me | solution 1 for GroundTheory.Global.ofMulDistribMulAction_gal_completion_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:22.056198+00:00
-- url     : https://prove2.me/submissions/bacc4547-8a2a-435f-803a-e7b219de987d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrand
import Definitions.Def_GroundTheory_GlobalFields_InfiniteNormIndex_LocalSymbol
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_LocalHerbrandInfinite
import Theorems.Thm_GroundTheory_Global_infiniteDecompositionMulEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_decomposition_smul_integerUnits
import Theorems.Thm_GroundTheory_Global_coe_decomposition_smul_integers
import Theorems.Thm_GroundTheory_Global_coe_decomposition_smul_units
import Theorems.Thm_GroundTheory_Global_coe_integerUnitsAddEquiv
import Theorems.Thm_GroundTheory_Global_cycSub_apply
import Theorems.Thm_GroundTheory_Global_decompositionMulEquiv_apply
import Theorems.Thm_GroundTheory_Global_normHom_apply
import Theorems.Thm_GroundTheory_Global_piRep_apply
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_GroupCoh_restrictEnd_apply
import Theorems.Thm_GroundTheory_LocalField_StableFiltration_coe_smul_F
import Theorems.Thm_GroundTheory_LocalField_coe_normUnits
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_ord_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_galRootsOfUnityHom_apply
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
import Theorems.Thm_P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.coe_decomposition_smul_integerUnits
attribute [local simp] GroundTheory.Global.coe_decomposition_smul_integers
attribute [local simp] GroundTheory.Global.coe_decomposition_smul_units
attribute [local simp] GroundTheory.Global.coe_integerUnitsAddEquiv
attribute [local simp] GroundTheory.Global.cycSub_apply
attribute [local simp] GroundTheory.Global.decompositionMulEquiv_apply
attribute [local simp] GroundTheory.Global.normHom_apply
attribute [local simp] GroundTheory.Global.piRep_apply
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk
attribute [local simp] GroundTheory.GroupCoh.restrictEnd_apply
attribute [local simp] GroundTheory.LocalField.StableFiltration.coe_smul_F
attribute [local simp] GroundTheory.LocalField.coe_normUnits
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.ord_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_galRootsOfUnityHom_apply
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddInt___apply_e3c2bd0048b0
attribute [local simp] P2M_GroundTheory_ProfCoh_galAddZ___apply_9150def5d083
attribute [local simp] P2M_GroundTheory_ProfCoh_galAdd___apply_d57b0a2a1b9a
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnityZ___apply_40a7d6b8f2a7
attribute [local simp] P2M_GroundTheory_ProfCoh_galRootsOfUnity___apply_600492b04171
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnitsZ___apply_2d4ee74d5783
attribute [local simp] P2M_GroundTheory_ProfCoh_galUnits___apply_5e27268f2c21


attribute [local simp] GroundTheory.Global.infiniteDecompositionMulEquiv_apply

set_option autoImplicit false
noncomputable section
open NumberField NumberField.InfinitePlace NumberField.InfinitePlace.Completion GroundTheory.GroupCoh
open scoped NumberField.LiesOver
open GroundTheory GroundTheory.Global
variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K)
  (w : InfinitePlace L) [w.LiesOver v]
namespace GroundTheory.Global
theorem _root_.solution (σ : Gal(w.Completion/v.Completion))
    (x : Additive w.Completionˣ) :
    Representation.ofMulDistribMulAction Gal(w.Completion/v.Completion) w.Completionˣ σ x =
      InfinitePlace.unitsRep v w σ x := by
  apply Additive.toMul.injective
  apply Units.ext
  rfl
end GroundTheory.Global
