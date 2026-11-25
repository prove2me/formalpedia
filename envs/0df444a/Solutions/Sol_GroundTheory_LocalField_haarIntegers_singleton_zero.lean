-- Prove2me | solution 1 for GroundTheory.LocalField.haarIntegers_singleton_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:13:30.557248+00:00
-- url     : https://prove2.me/submissions/72096f6a-191b-4bef-bf5d-30f007779370

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_haarIntegers_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard_nnreal
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
  [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution : haarIntegers K {0} = 0 := by
  have hq : (1 : ℝ≥0) < (residueCard K : ℝ≥0) := one_lt_residueCard_nnreal
  have ht : Tendsto (fun n : ℕ => (((residueCard K : ℝ≥0) ^ (-(n : ℤ)) : ℝ≥0) : ℝ≥0∞)) atTop
      (𝓝 0) := by
    rw [← ENNReal.coe_zero, ENNReal.tendsto_coe]
    have e : (fun n : ℕ => (residueCard K : ℝ≥0) ^ (-(n : ℤ))) =
        fun n : ℕ => ((residueCard K : ℝ≥0)⁻¹) ^ n := by
      funext n
      rw [zpow_neg, zpow_natCast, inv_pow]
    rw [e]
    exact NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (inv_lt_one_of_one_lt₀ hq)
  refine le_antisymm (ge_of_tendsto' ht fun n => ?_) (by simp)
  rw [← haarIntegers_valBall]
  exact measure_mono (Set.singleton_subset_iff.mpr (zero_mem _))
end GroundTheory.LocalField
