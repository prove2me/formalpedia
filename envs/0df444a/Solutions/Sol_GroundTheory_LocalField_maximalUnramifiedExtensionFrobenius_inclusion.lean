-- Prove2me | solution 1 for GroundTheory.LocalField.maximalUnramifiedExtensionFrobenius_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:42.238036+00:00
-- url     : https://prove2.me/submissions/b294b0ec-df2c-4c93-a7b7-8e2f324a31e8

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
import Theorems.Thm_GroundTheory_LocalField_integerToCompleted_apply
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_ramificationIndex_eq_one
import Theorems.Thm_GroundTheory_LocalField_card_residueField_of_unramified
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_frobenius_apply_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionGaloisEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_natCast_card_pow_sub_one_ne_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
attribute [local simp] GroundTheory.LocalField.Abstract.cosetConj_mk
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.galoisEquivResidue_apply
attribute [local simp] GroundTheory.LocalField.maximalUnramifiedExtensionGaloisEquiv_apply
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.integerToCompleted_apply

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open IsLocalRing ValuativeRel
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
  [IsGalois K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω
namespace GroundTheory.LocalField
theorem _root_.solution {L : IntermediateField K Ω}
    (hL : IsUnramifiedSubextension L) (y : L) :
    letI := hL.1
    ((maximalUnramifiedExtensionFrobenius K Ω
      (IntermediateField.inclusion hL.le_maximalUnramifiedExtension y) : 𝔼) : Ω) =
      ((frobenius K L hL.ramificationIndex_eq_one y : L) : Ω) := by
  have := hL.1
  have h := hL.ramificationIndex_eq_one
  have hle := hL.le_maximalUnramifiedExtension
  obtain ⟨ξ, hξ, htop⟩ := exists_isPrimitiveRoot_adjoin_eq_top_of_unramified K L h
  have hn : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  rw [card_residueField_of_unramified K L h] at hξ
  have hm := natCast_card_pow_sub_one_ne_zero (K := K) hn
  have key : (maximalUnramifiedExtension K Ω).val.comp
      ((maximalUnramifiedExtensionFrobenius K Ω).toAlgHom.comp (IntermediateField.inclusion hle)) =
      L.val.comp (frobenius K L h).toAlgHom := by
    refine AlgHom.ext_of_adjoin_eq_top (algebra_adjoin_eq_top_of_adjoin_eq_top htop) ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h1 : (IntermediateField.inclusion hle ξ) ^ (Nat.card 𝓀[K] ^ Module.finrank K L - 1) = 1 := by
      rw [← map_pow, hξ.pow_eq_one, map_one]
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm h1,
      frobenius_apply_of_pow_eq_one h hm hξ.pow_eq_one]
    simp
  have hk := congrArg (fun f : L →ₐ[K] Ω ↦ f y) key
  simpa only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] using hk
end GroundTheory.LocalField
