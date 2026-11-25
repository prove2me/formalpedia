-- Prove2me | solution 1 for GroundTheory.LocalField.localEpsilon_of_not_isUnramified_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:01:24.329801+00:00
-- url     : https://prove2.me/submissions/2f840fee-8655-46bf-980c-7943f6e08682

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Definitions.Def_GroundTheory_LocalFields_PadicLogHom
import Definitions.Def_GroundTheory_LocalFields_LocalZetaEpsilon
import Theorems.Thm_GroundTheory_LocalField_modulus_cpow_eq_qcpow
import Theorems.Thm_GroundTheory_LocalField_localEpsilon_of_not_isUnramified
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
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
variable [MeasurableSpace K] [BorelSpace K]
variable {χ : Kˣ →* ℂˣ} {ψ : AddChar K Circle}
namespace GroundTheory.LocalField
theorem _root_.solution (hr : ¬ IsUnramifiedChar χ) (s : ℂ) :
    localEpsilon χ ψ s =
      (residueCard K : ℂ) ^ (((addCharConductor ψ - quasiCharConductor χ : ℤ) : ℂ) * s) *
        (((residueCard K : ℝ) ^ ((addCharConductor ψ : ℝ) / 2) : ℝ) : ℂ) *
        ∫ x in (valBall K (addCharConductor ψ - quasiCharConductor χ) : Set K) \
            valBall K (addCharConductor ψ - quasiCharConductor χ + 1),
          quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K := by
  set m : ℤ := addCharConductor ψ - quasiCharConductor χ
  have hS : MeasurableSet ((valBall K m : Set K) \ valBall K (m + 1)) :=
    (measurableSet_valBall m).diff (measurableSet_valBall (m + 1))
  rw [localEpsilon_of_not_isUnramified hr]
  rw [setIntegral_congr_fun hS (g := fun x => (residueCard K : ℂ) ^ ((m : ℂ) * s) *
    (quasiCharExt χ⁻¹ x * (ψ x : ℂ))) fun x hx => by
      have hx0 : x ≠ 0 := fun h => hx.2 (h ▸ zero_mem _)
      have hord : ord x = m := by
        have a := (mem_valBall_iff_le_ord hx0).mp hx.1
        have b := mt (mem_valBall_iff_le_ord hx0).mpr hx.2
        omega
      simp only
      rw [modulus_cpow_eq_qcpow hx0, hord]
      ring_nf]
  rw [integral_const_mul, selfDualMeasure, Measure.restrict_smul, integral_smul_nnreal_measure,
    NNReal.smul_def, Complex.real_smul, NNReal.coe_rpow, NNReal.coe_natCast]
  ring
end GroundTheory.LocalField
