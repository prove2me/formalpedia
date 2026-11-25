-- Prove2me | solution 1 for GroundTheory.LocalField.inversion_const_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:02:55.098862+00:00
-- url     : https://prove2.me/submissions/d8272bce-e816-4bae-ba9e-d8a51f3d9e0e

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_one_lt_residueCard
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
omit [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (n : ℤ) {r : ℝ} (hr : 0 ≤ r) :
    (residueCard K : ℝ) ^ (-n) * r ^ 2 = 1 ↔ r = (residueCard K : ℝ) ^ ((n : ℝ) / 2) := by
  have hq : (0 : ℝ) < residueCard K := by exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have hsq : ((residueCard K : ℝ) ^ ((n : ℝ) / 2)) ^ 2 = (residueCard K : ℝ) ^ n := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hne : (residueCard K : ℝ) ^ (-n) ≠ 0 := zpow_ne_zero _ hq.ne'
  constructor
  · intro h
    have h2 : r ^ 2 = (residueCard K : ℝ) ^ n := by
      have := congrArg (fun t => (residueCard K : ℝ) ^ n * t) h
      simp only [mul_one, ← mul_assoc] at this
      rwa [← zpow_add₀ hq.ne', add_neg_cancel, zpow_zero, one_mul] at this
    rw [← hsq] at h2
    exact (pow_left_inj₀ hr (Real.rpow_nonneg hq.le _) two_ne_zero).mp h2
  · intro h
    rw [h, hsq, ← zpow_add₀ hq.ne', neg_add_cancel, zpow_zero]
end GroundTheory.LocalField
