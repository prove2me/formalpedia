-- Prove2me | solution 1 for GroundTheory.LocalField.multHaar_unitFiltrationUnits_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:01:35.430046+00:00
-- url     : https://prove2.me/submissions/28665b0e-c324-4a94-a40d-fd67c9caea1d

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_haarIntegers_valBall
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
import Theorems.Thm_GroundTheory_LocalField_mem_unitFiltrationUnits_zero_iff
import Theorems.Thm_GroundTheory_LocalField_mem_valBall_one_iff
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_one_iff
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residueCard_nnreal_ne_zero
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_fst
import Theorems.Thm_GroundTheory_LocalField_unitsEquivResidueProd_symm_apply
import Theorems.Thm_GroundTheory_LocalField_valBall_antitone
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
theorem _root_.solution :
    multHaar K (unitFiltrationUnits K 0 : Set Kˣ) = 1 := by
  rw [multHaar_apply]
  have himg : Units.val '' (unitFiltrationUnits K 0 : Set Kˣ) =
      (valBall K 0 : Set K) \ valBall K 1 := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff] at hu
      exact ⟨mem_valBall_zero_iff.mpr (le_of_eq hu), fun h => (mem_valBall_one_iff.mp h).ne hu⟩
    · rintro ⟨h0, h1⟩
      have hx0 : x ≠ 0 := fun h => h1 (h ▸ zero_mem _)
      refine ⟨Units.mk0 x hx0, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_unitFiltrationUnits_zero_iff, Units.val_mk0]
      have hle : valuation K x ≤ 1 := mem_valBall_zero_iff.mp h0
      have hnlt : ¬ valuation K x < 1 := fun h => h1 (mem_valBall_one_iff.mpr h)
      exact le_antisymm hle (not_lt.mp hnlt)
  rw [himg]
  have hd : ∀ x ∈ (valBall K 0 : Set K) \ valBall K 1, ((modulus x : ℝ≥0∞))⁻¹ = 1 := by
    rintro x ⟨h0, h1⟩
    have hx0 : x ≠ 0 := fun h => h1 (h ▸ zero_mem _)
    have hord : ord x = 0 := by
      have a := (mem_valBall_iff_le_ord hx0).mp h0
      have b := mt (mem_valBall_iff_le_ord hx0).mpr h1
      omega
    rw [modulus_eq_one_iff.mpr ⟨hx0, hord⟩]
    simp
  have hm := (measurableSet_valBall (K := K) 0).diff (measurableSet_valBall 1)
  rw [setLIntegral_congr_fun hm hd, setLIntegral_const, one_mul,
    measure_sdiff (valBall_antitone (by norm_num)) (measurableSet_valBall 1).nullMeasurableSet
      (isCompact_valBall 1).measure_lt_top.ne,
    haarIntegers_valBall, haarIntegers_valBall, neg_zero, zpow_zero, ENNReal.coe_one, zpow_neg_one,
    ENNReal.coe_inv residueCard_nnreal_ne_zero, ENNReal.coe_natCast, multHaarConst,
    ENNReal.inv_mul_cancel one_sub_inv_residueCard_ne_zero
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
end GroundTheory.LocalField
