-- Prove2me | solution 1 for GroundTheory.Global.Modulus.congruenceSubgroup_eq_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:52:46.800235+00:00
-- url     : https://prove2.me/submissions/94240c82-b06c-4297-958a-d2c31c4730a4

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeCharRayClass
import Definitions.Def_GroundTheory_GlobalFields_ClassFieldConsequences_CongruenceSubgroupLeStandardOpenSubgroup
import Theorems.Thm_GroundTheory_Global_Modulus_exponent_eq_zero_iff
import Theorems.Thm_GroundTheory_Global_Modulus_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Global_Modulus_mem_idelesOneMod
import Theorems.Thm_GroundTheory_Global_HeckeCharacter_toIdele_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleClassGroup_ideleModule_mk
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteComponent
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_finiteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_infiniteProj_diagonal
import Theorems.Thm_GroundTheory_Global_IdeleGroup_coe_unitsToUnits
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteAdeleSingle_apply_self
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteComponent_finiteUnitsSingle
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteProj_finiteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_finiteUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_IdeleGroup_infiniteProj_infiniteEmbedding
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_finiteLevel
import Theorems.Thm_GroundTheory_Global_IdeleGroup_mem_standardOpenSubgroup_iff_toFinite_mem
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_fst
import Theorems.Thm_GroundTheory_Global_IdeleGroup_prodRestrictedEquiv_apply_snd
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toFinite_ofFinite
import Theorems.Thm_GroundTheory_Global_IdeleGroup_toInfinite_ofFinite
import Theorems.Thm_GroundTheory_Global_RestrictedProduct_continuousUnitsEquiv_apply
import Theorems.Thm_GroundTheory_Global_coe_circleToUnits
import Theorems.Thm_GroundTheory_Global_residueFieldEquiv_mk
import Theorems.Thm_GroundTheory_Global_unitsLevel_antitone
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.Global.HeckeCharacter.toIdele_diagonal
attribute [local simp] GroundTheory.Global.IdeleClassGroup.ideleModule_mk
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteComponent
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_finiteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_infiniteProj_diagonal
attribute [local simp] GroundTheory.Global.IdeleGroup.coe_unitsToUnits
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteAdeleSingle_apply_self
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteComponent_finiteUnitsSingle
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteProj_finiteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.finiteUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.IdeleGroup.infiniteProj_infiniteEmbedding
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_fst
attribute [local simp] GroundTheory.Global.IdeleGroup.prodRestrictedEquiv_apply_snd
attribute [local simp] GroundTheory.Global.IdeleGroup.toFinite_ofFinite
attribute [local simp] GroundTheory.Global.IdeleGroup.toInfinite_ofFinite
attribute [local simp] GroundTheory.Global.RestrictedProduct.continuousUnitsEquiv_apply
attribute [local simp] GroundTheory.Global.coe_circleToUnits
attribute [local simp] GroundTheory.Global.residueFieldEquiv_mk



set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain WithZero Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
open IdeleGroup
open GroundTheory.Global.Modulus
variable (𝔪 : Modulus K)
namespace GroundTheory.Global.Modulus
theorem _root_.solution :
    𝔪.congruenceSubgroup = 𝔪.idelesOneMod ⊓ standardOpenSubgroup K := by
  ext x
  rw [Subgroup.mem_inf, mem_congruenceSubgroup, mem_idelesOneMod,
    mem_standardOpenSubgroup_iff_toFinite_mem, mem_finiteLevel]
  simp only [finiteComponent_toFinite, Pi.zero_apply]
  constructor
  · rintro ⟨hf, hi⟩
    exact ⟨⟨fun v _ ↦ hf v, hi⟩, fun v ↦ unitsLevel_antitone v (Nat.zero_le _) (hf v)⟩
  · rintro ⟨⟨hf, hi⟩, h0⟩
    refine ⟨fun v ↦ ?_, hi⟩
    by_cases hv : v.asIdeal ∣ 𝔪.ideal
    · exact hf v hv
    · rw [(𝔪.exponent_eq_zero_iff v).2 hv]
      exact h0 v
end GroundTheory.Global.Modulus
