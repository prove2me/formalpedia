-- Prove2me | solution 1 for GroundTheory.LocalField.measure_valBall
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:21:12.98409+00:00
-- url     : https://prove2.me/submissions/b04f906f-899a-4f10-9c8e-2a2d492fd82a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_PadicLogSeries
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_LocalFourierHaar
import Theorems.Thm_GroundTheory_LocalField_residueCard_nnreal_ne_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_measure_valBall_eq_mul_succ
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
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
attribute [local simp] GroundTheory.LocalField.coe_homeomorphOfIsAlgebraic
attribute [local simp] GroundTheory.LocalField.residueAlgEquiv_residue
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_fst
attribute [local simp] GroundTheory.LocalField.unitsEquivResidueProd_symm_apply


attribute [local simp] GroundTheory.LocalField.modulus_zero
attribute [local simp] GroundTheory.LocalField.modulus_eq_zero
attribute [local simp] GroundTheory.LocalField.modulus_one

set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter TopologicalSpace
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [μ.IsAddHaarMeasure]
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℤ) :
    μ (valBall K n) = ((residueCard K : ℝ≥0) ^ (-n) : ℝ≥0) * μ (valBall K 0) := by
  have hq0 := residueCard_nnreal_ne_zero (K := K)
  have hq : ((residueCard K : ℝ≥0) : ℝ≥0∞) ≠ 0 := by exact_mod_cast hq0
  have hqt : ((residueCard K : ℝ≥0) : ℝ≥0∞) ≠ ∞ := ENNReal.coe_ne_top
  have hcast : ((residueCard K : ℕ) : ℝ≥0∞) = ((residueCard K : ℝ≥0) : ℝ≥0∞) := rfl
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have h := measure_valBall_eq_mul_succ μ (k : ℤ)
    rw [ih, hcast] at h
    have : μ (valBall K (k + 1)) = ((residueCard K : ℝ≥0) : ℝ≥0∞)⁻¹ *
        (((residueCard K : ℝ≥0) ^ (-(k : ℤ)) : ℝ≥0) * μ (valBall K 0)) := by
      rw [h, ← mul_assoc, ENNReal.inv_mul_cancel hq hqt, one_mul]
    have e : ((residueCard K : ℝ≥0))⁻¹ * (residueCard K : ℝ≥0) ^ (-(k : ℤ)) =
        (residueCard K : ℝ≥0) ^ (-((k : ℤ) + 1)) := by
      rw [show -((k : ℤ) + 1) = -1 + -(k : ℤ) by ring, zpow_add₀ hq0, zpow_neg_one]
    rw [this, ← mul_assoc, ← ENNReal.coe_inv hq0, ← ENNReal.coe_mul, e]
  | pred k ih =>
    have h := measure_valBall_eq_mul_succ μ (-(k : ℤ) - 1)
    rw [sub_add_cancel, ih, hcast] at h
    have e : (residueCard K : ℝ≥0) * (residueCard K : ℝ≥0) ^ (-(-(k : ℤ))) =
        (residueCard K : ℝ≥0) ^ (-(-(k : ℤ) - 1)) := by
      rw [show -(-(k : ℤ) - 1) = 1 + -(-(k : ℤ)) by ring, zpow_add₀ hq0, zpow_one]
    rw [h, ← mul_assoc, ← ENNReal.coe_mul, e]
end GroundTheory.LocalField
