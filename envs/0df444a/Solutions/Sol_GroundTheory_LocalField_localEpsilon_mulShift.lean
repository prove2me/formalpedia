-- Prove2me | solution 1 for GroundTheory.LocalField.localEpsilon_mulShift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:11:50.100027+00:00
-- url     : https://prove2.me/submissions/f5ea1068-8d79-49e9-9485-f20904f711e0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Theorems.Thm_GroundTheory_LocalField_quasiCharExt_mul
import Theorems.Thm_GroundTheory_LocalField_mem_shellSet_iff
import Theorems.Thm_GroundTheory_LocalField_zero_notMem_shellSet
import Theorems.Thm_GroundTheory_LocalField_ofReal_modulus_inv_eq
import Theorems.Thm_GroundTheory_LocalField_addCharConductor_mulShift
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_integral_comp_mul_left
import Theorems.Thm_GroundTheory_LocalField_localEpsilon_of_isUnramified
import Theorems.Thm_GroundTheory_LocalField_localEpsilon_of_not_isUnramified_eq
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_cpow_eq_qcpow
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_ofReal_qrpow
import Theorems.Thm_GroundTheory_LocalField_ord_mul
import Theorems.Thm_GroundTheory_LocalField_qcpow_mul_qcpow
import Theorems.Thm_GroundTheory_LocalField_quasiCharExt_units
import Theorems.Thm_GroundTheory_LocalField_quasiChar_apply_of_isUnramified
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
theorem _root_.solution (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) (a : Kˣ) (s : ℂ) :
    localEpsilon χ (ψ.mulShift (a : K)) s =
      ((χ a : ℂˣ) : ℂ) * ((modulus (a : K) : ℝ) : ℂ) ^ (s - 1 / 2) * localEpsilon χ ψ s := by
  have hn := addCharConductor_mulShift hψ hψ1 a.ne_zero
  set k := ord (a : K)
  set n := addCharConductor ψ
  by_cases hu : IsUnramifiedChar χ
  · set α := ((χ (unifUnit K) : ℂˣ) : ℂ)
    have hα : α ≠ 0 := (χ _).ne_zero
    have hχa : ((χ a : ℂˣ) : ℂ) = α ^ k := by
      rw [quasiChar_apply_of_isUnramified hu a, Units.val_zpow_eq_zpow_val]
    rw [localEpsilon_of_isUnramified hu, localEpsilon_of_isUnramified hu, hn, hχa,
      modulus_cpow_eq_qcpow a.ne_zero,
      show -(n - k) = k + -n by ring, zpow_add₀ hα]
    have e : (residueCard K : ℂ) ^ (((n - k : ℤ) : ℂ) * (s - 1 / 2)) =
        (residueCard K : ℂ) ^ (-(k : ℂ) * (s - 1 / 2)) *
          (residueCard K : ℂ) ^ ((n : ℂ) * (s - 1 / 2)) := by
      rw [qcpow_mul_qcpow]
      congr 1
      push_cast
      ring
    rw [e]
    ring
  · set c := quasiCharConductor χ
    set A := ∫ x in (valBall K (n - c) : Set K) \ valBall K (n - c + 1),
      quasiCharExt χ⁻¹ x * (ψ x : ℂ) ∂haarIntegers K

    have hA : ∫ x in (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1),
        quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ) ∂haarIntegers K =
        ((((modulus (a : K) : ℝ))⁻¹ : ℝ) : ℂ) * (((χ a : ℂˣ) : ℂ) * A) := by
      have hS := (measurableSet_valBall (K := K) (n - k - c)).diff
        (measurableSet_valBall (n - k - c + 1))
      have hS' := (measurableSet_valBall (K := K) (n - c)).diff (measurableSet_valBall (n - c + 1))
      let H : K → ℂ := ((valBall K (n - c) : Set K) \ valBall K (n - c + 1)).indicator
        fun y => ((χ a : ℂˣ) : ℂ) * (quasiCharExt χ⁻¹ y * (ψ y : ℂ))
      have hχa : quasiCharExt χ⁻¹ (a : K) * ((χ a : ℂˣ) : ℂ) = 1 := by
        rw [quasiCharExt_units, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
          inv_mul_cancel₀ (χ a).ne_zero]
      have hpt : ∀ x : K, ((valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1)).indicator
          (fun x => quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ)) x = H ((a : K) * x) := by
        intro x
        simp only [H]
        by_cases hx : x = 0
        · rw [hx, mul_zero, Set.indicator_of_notMem (zero_notMem_shellSet _),
            Set.indicator_of_notMem (zero_notMem_shellSet _)]
        have hax : (a : K) * x ≠ 0 := mul_ne_zero a.ne_zero hx
        have hiff : x ∈ (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1) ↔
            (a : K) * x ∈ (valBall K (n - c) : Set K) \ valBall K (n - c + 1) := by
          rw [mem_shellSet_iff hx, mem_shellSet_iff hax, ord_mul a.ne_zero hx]
          omega
        by_cases hm : x ∈ (valBall K (n - k - c) : Set K) \ valBall K (n - k - c + 1)
        · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hiff.mp hm), quasiCharExt_mul,
            AddChar.mulShift_apply]
          linear_combination (quasiCharExt χ⁻¹ x * (ψ ((a : K) * x) : ℂ)) * hχa.symm
        · rw [Set.indicator_of_notMem hm, Set.indicator_of_notMem (mt hiff.mpr hm)]
      rw [← integral_indicator hS, show (fun x => ((valBall K (n - k - c) : Set K) \
          valBall K (n - k - c + 1)).indicator
          (fun x => quasiCharExt χ⁻¹ x * ((ψ.mulShift (a : K)) x : ℂ)) x) =
          fun x => H ((a : K) * x) from funext hpt,
        integral_comp_mul_left (haarIntegers K) a.ne_zero H, Complex.real_smul,
        integral_indicator hS', integral_const_mul]
    rw [localEpsilon_of_not_isUnramified_eq hu, localEpsilon_of_not_isUnramified_eq hu, hn, hA,
      ofReal_modulus_inv_eq, modulus_cpow_eq_qcpow a.ne_zero, ofReal_qrpow, ofReal_qrpow]
    have e : (residueCard K : ℂ) ^ (((n - k - c : ℤ) : ℂ) * s) *
        (residueCard K : ℂ) ^ ((((n - k : ℤ) : ℝ) / 2 : ℝ) : ℂ) *
          (residueCard K : ℂ) ^ ((k : ℤ) : ℂ) =
        (residueCard K : ℂ) ^ (-(k : ℂ) * (s - 1 / 2)) *
          ((residueCard K : ℂ) ^ (((n - c : ℤ) : ℂ) * s) *
            (residueCard K : ℂ) ^ ((((n : ℤ) : ℝ) / 2 : ℝ) : ℂ)) := by
      simp only [qcpow_mul_qcpow]
      congr 1
      push_cast
      ring
    linear_combination (((χ a : ℂˣ) : ℂ) * A) * e
end GroundTheory.LocalField
