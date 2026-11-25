-- Prove2me | solution 1 for GroundTheory.LocalField.setIntegral_ordShell_quasiChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:20:57.385015+00:00
-- url     : https://prove2.me/submissions/5b646da0-5fee-4ef6-b320-76ef6a79227f

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Theorems.Thm_GroundTheory_LocalField_isUnramifiedChar_iff
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_measurableSet_ordShell
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_selfDual_apply
import Theorems.Thm_GroundTheory_LocalField_setIntegral_ordShell_eq_zero
import Theorems.Thm_GroundTheory_LocalField_setIntegral_ordShell_mul
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
variable [MeasurableSpace K] [BorelSpace K] {χ : Kˣ →* ℂˣ}
open scoped Classical
namespace GroundTheory.LocalField
theorem _root_.solution (hχ : Continuous χ) (k : ℤ) :
    ∫ u in ordShell K k, ((χ u : ℂˣ) : ℂ) ∂multHaar K =
      if IsUnramifiedChar χ then ((χ (unifUnit K) : ℂˣ) : ℂ) ^ k else 0 := by
  have hk : ord ((unifUnit K ^ k : Kˣ) : K) + 0 = k := by rw [ord_unifUnit_zpow, add_zero]
  have e := setIntegral_ordShell_mul (fun u : Kˣ => ((χ u : ℂˣ) : ℂ)) (unifUnit K ^ k) 0
  rw [hk] at e
  rw [e]
  simp only [map_mul, Units.val_mul, map_zpow, Units.val_zpow_eq_zpow_val]
  rw [integral_const_mul]
  split_ifs with h
  · have hone : ∀ u ∈ ordShell K 0, ((χ u : ℂˣ) : ℂ) = 1 := fun u hu => by
      rw [(isUnramifiedChar_iff.mp h) u hu, Units.val_one]
    rw [setIntegral_congr_fun (measurableSet_ordShell 0) hone, setIntegral_const,
      measureReal_def, multHaar_ordShell, ENNReal.toReal_one, one_smul, mul_one]
  · obtain ⟨v, hv, hv1⟩ : ∃ v ∈ unitFiltrationUnits K 0, χ v ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      exact h fun v hv => MonoidHom.mem_ker.mpr (hcon v hv)
    rw [setIntegral_ordShell_eq_zero (fun u => ((χ u : ℂˣ) : ℂ))
      (mem_unitFiltrationUnits_zero_iff_ord.mp hv) (a := ((χ v : ℂˣ) : ℂ))
      (fun h1 => hv1 (Units.val_eq_one.mp h1)) 0 (fun u _ => by simp), mul_zero]
end GroundTheory.LocalField
