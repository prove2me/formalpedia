-- Prove2me | solution 1 for GroundTheory.LocalField.integral_multHaar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:18:27.228818+00:00
-- url     : https://prove2.me/submissions/a151715a-fbe2-4c25-b63e-5b634cc8eaf9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_pos
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
variable [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : K → E) :
    ∫ u, f u ∂(multHaar K) =
      (multHaarConst K).toReal • ∫ x in {0}ᶜ, ((modulus x : ℝ))⁻¹ • f x ∂(haarIntegers K) := by
  rw [← measurableEmbedding_units_val.integral_map, multHaar,
    measurableEmbedding_units_val.map_comap, range_units_val, Measure.restrict_smul,
    integral_smul_measure,
    setIntegral_withDensity_eq_setIntegral_toReal_smul measurable_modulus_inv
      (ae_restrict_of_forall_mem (measurableSet_singleton 0).compl fun x hx =>
        ENNReal.inv_lt_top.mpr (ENNReal.coe_pos.mpr (modulus_pos hx))) f
      (measurableSet_singleton 0).compl]
  congr 1
  refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x _ => ?_
  simp [ENNReal.toReal_inv]
end GroundTheory.LocalField
