-- Prove2me | solution 1 for GroundTheory.ProfCoh.integer_subgroup_torsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:24:37.474006+00:00
-- url     : https://prove2.me/submissions/2bba2dac-cfc6-4853-8b04-ae21ec8d311a

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_LocalField_coe_smul_integerUnits
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_ProfCoh_coe_torsNRep_apply
import Theorems.Thm_GroundTheory_ProfCoh_modNRep_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.coe_smul_integerUnits
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply
attribute [local simp] GroundTheory.ProfCoh.coe_torsNRep_apply
attribute [local simp] GroundTheory.ProfCoh.modNRep_mk



set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
variable {F : Type*} [Field F] [ValuativeRel F]
namespace GroundTheory.ProfCoh
theorem _root_.solution {m : ℕ} (hm : (m : F) ≠ 0) (H : AddSubgroup 𝒪[F]) (a : H)
    (ha : m • a = 0) : a = 0 := by
  have hm' : (m : 𝒪[F]) ≠ 0 := fun h ↦ hm (by simpa using congrArg Subtype.val h)
  have h := congrArg (fun x : H ↦ (x : 𝒪[F])) ha
  simp only [AddSubgroup.coe_nsmul, nsmul_eq_mul, ZeroMemClass.coe_zero, mul_eq_zero, hm',
    false_or] at h
  exact Subtype.ext h
end GroundTheory.ProfCoh
