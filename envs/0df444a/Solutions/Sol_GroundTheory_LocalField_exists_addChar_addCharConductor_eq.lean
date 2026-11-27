-- Prove2me | solution 1 for GroundTheory.LocalField.exists_addChar_addCharConductor_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:11.712981+00:00
-- url     : https://prove2.me/submissions/d083562d-49e4-4a8b-b11a-e2b7fe39f0fe

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalFourierExistence
import Theorems.Thm_GroundTheory_LocalField_exists_addChar_addCharConductor_eq_zero
import Theorems.Thm_GroundTheory_LocalField_addCharConductor_mulShift
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_mulShift_ne_one
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
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
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one
attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.selfDual_apply
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter
open scoped WithZero Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℤ) :
    ∃ ψ : AddChar K Circle, Continuous ψ ∧ ψ ≠ 1 ∧ addCharConductor ψ = n := by
  obtain ⟨ψ, hc, hne, h0⟩ := exists_addChar_addCharConductor_eq_zero (K := K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have h0ϖ : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have ha : (ϖ : K) ^ (-n) ≠ 0 := zpow_ne_zero _ h0ϖ
  refine ⟨ψ.mulShift ((ϖ : K) ^ (-n)), continuous_mulShift hc _, mulShift_ne_one hne ha, ?_⟩
  have hord : ord ((ϖ : K) ^ (-n)) = -n := by
    simp [ord, map_zpow₀, normalizedValuation_uniformizer hϖ]
  rw [addCharConductor_mulShift hc hne ha, h0, hord]
  ring
end GroundTheory.LocalField
