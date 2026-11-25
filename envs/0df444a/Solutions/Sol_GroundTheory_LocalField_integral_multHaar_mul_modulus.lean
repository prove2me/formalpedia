-- Prove2me | solution 1 for GroundTheory.LocalField.integral_multHaar_mul_modulus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:22:12.880816+00:00
-- url     : https://prove2.me/submissions/174babcc-c3da-4a95-be86-624c705930bc

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Theorems.Thm_GroundTheory_LocalField_haarIntegers_singleton_zero
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_integral_multHaar
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
  [MeasurableSpace K] [BorelSpace K]
namespace GroundTheory.LocalField
theorem _root_.solution (h : K → ℂ) :
    ∫ u, h u * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      (multHaarConst K).toReal * ∫ x, h x ∂haarIntegers K := by
  rw [integral_multHaar (fun x => h x * ((modulus x : ℝ) : ℂ)), Complex.real_smul]
  congr 1
  have hae : ∀ᵐ x ∂haarIntegers K, x ∈ ({0}ᶜ : Set K) := by
    rw [ae_iff]
    simpa using haarIntegers_singleton_zero (K := K)
  conv_rhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]
  refine setIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
  have hm : ((modulus x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos hx).ne'
  rw [Complex.real_smul, Complex.ofReal_inv, mul_comm, mul_assoc, mul_inv_cancel₀ hm, mul_one]
end GroundTheory.LocalField
