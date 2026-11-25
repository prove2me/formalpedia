-- Prove2me | solution 1 for GroundTheory.LocalField.frobenius_integer_sub_pow_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:47:22.589939+00:00
-- url     : https://prove2.me/submissions/395b0d12-2cd2-45c3-83fb-1a53d11420f9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Theorems.Thm_GroundTheory_LocalField_Abstract_cosetConj_mk
import Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_ramificationIndex_eq_one
import Theorems.Thm_GroundTheory_LocalField_card_residueField_of_unramified
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_frobenius_apply_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_frobenius_sub_pow_mem_maximalIdeal
import Theorems.Thm_GroundTheory_LocalField_galoisEquivResidue_apply
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one
import Theorems.Thm_GroundTheory_LocalField_maximalUnramifiedExtensionGaloisEquiv_apply
import Theorems.Thm_GroundTheory_LocalField_mem_maximalUnramifiedExtension_iff
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



set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
variable [IsGalois K Ω]
namespace GroundTheory.LocalField
theorem _root_.solution (x : 𝒪[𝔼]) :
    integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x -
      x ^ Nat.card 𝓀[K] ∈ 𝓂[𝔼] := by
  obtain ⟨L, hL, hxL⟩ := mem_maximalUnramifiedExtension_iff.mp (x : 𝔼).2
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
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h1 : (IntermediateField.inclusion hle ξ) ^ (Nat.card 𝓀[K] ^ Module.finrank K L - 1) = 1 := by
      rw [← map_pow, hξ.pow_eq_one, map_one]
    simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom]
    rw [maximalUnramifiedExtensionFrobenius_apply_of_pow_eq_one hm h1,
      frobenius_apply_of_pow_eq_one h hm hξ.pow_eq_one]
    simp
  set z : 𝒪[L] := ⟨⟨(x : 𝔼), hxL⟩, (mem_integer_intermediateField_iff L _).mpr
    ((mem_integer_intermediateField_iff 𝔼 x).mp x.2)⟩
  have hz := frobenius_sub_pow_mem_maximalIdeal K L h z
  rw [mem_maximalIdeal_intermediateField_iff] at hz ⊢
  have hk := congrArg (fun f : L →ₐ[K] Ω ↦ f ⟨(x : 𝔼), hxL⟩) key
  simp only [AlgHom.comp_apply, IntermediateField.coe_val, AlgEquiv.coe_toAlgHom] at hk
  convert hz using 2
  change ((maximalUnramifiedExtensionFrobenius K Ω (IntermediateField.inclusion hle ⟨(x : 𝔼), hxL⟩) :
      𝔼) : Ω) - _ = ((frobenius K L h ⟨(x : 𝔼), hxL⟩ : L) : Ω) - _
  rw [hk]
  rfl
end GroundTheory.LocalField
