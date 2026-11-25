-- Prove2me | solution 1 for GroundTheory.LocalField.lowerIndex_eq_addVal_of_adjoin_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:23:37.281873+00:00
-- url     : https://prove2.me/submissions/65819bc0-a1dd-416a-9b14-1f96461b06b7

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Ramification
import Definitions.Def_GroundTheory_LocalFields_Monogenic
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Theorems.Thm_GroundTheory_LocalField_le_lowerIndex_iff
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_le
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_one
import Theorems.Thm_GroundTheory_LocalField_lowerIndex_inv
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
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.lowerIndex_one
attribute [local simp] GroundTheory.LocalField.lowerIndex_inv

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing IsDiscreteValuationRing Polynomial
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
namespace GroundTheory.LocalField
theorem _root_.solution {x : 𝒪[L]} (hx : Algebra.adjoin 𝒪[K] {x} = ⊤)
    (σ : L ≃ₐ[K] L) : lowerIndex K L σ = addVal 𝒪[L] (integerAlgEquiv K L σ x - x) := by
  refine le_antisymm (lowerIndex_le σ x) ?_
  rw [le_lowerIndex_iff]
  intro z
  have hz : z ∈ Algebra.adjoin 𝒪[K] {x} := hx ▸ trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  rw [addVal_le_iff_dvd]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← aeval_algHom_apply, ← eval_map_algebraMap, ← eval_map_algebraMap]
  exact sub_dvd_eval_sub _ _ _
end GroundTheory.LocalField
