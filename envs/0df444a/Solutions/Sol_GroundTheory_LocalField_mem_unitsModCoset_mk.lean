-- Prove2me | solution 1 for GroundTheory.LocalField.mem_unitsModCoset_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:38:30.727457+00:00
-- url     : https://prove2.me/submissions/d10d4158-9e13-4ea8-ba47-6787dcf137bf

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Theorems.Thm_GroundTheory_LocalField_mem_unitsModCoset
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
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
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution {c : ℕ} {x : Kˣ} (hx : x ∈ unitFiltrationUnits K 0) :
    x ∈ unitsModCoset (QuotientGroup.mk ⟨x, hx⟩ : unitsModFiltration K c) := by
  have h := QuotientGroup.out_eq' (QuotientGroup.mk ⟨x, hx⟩ : unitsModFiltration K c)
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  simpa [mem_unitsModCoset, unitsModRep] using h
end GroundTheory.LocalField
