-- Prove2me | solution 1 for GroundTheory.LocalField.localFourier_eq_zero_of_notMem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:59:19.516991+00:00
-- url     : https://prove2.me/submissions/b507a8bb-c019-4acd-a402-62c9e92b1ff1

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Theorems.Thm_GroundTheory_LocalField_eq_zero_of_eq_mul_of_ne_one
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
open ValuativeRel MeasureTheory Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [μ.IsAddHaarMeasure]
variable (ψ : AddChar K Circle)
variable {ψ} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
include hψ hψ1
namespace GroundTheory.LocalField
theorem _root_.solution {f : K → ℂ} {N : ℤ}
    (hfN : ∀ x, ∀ h ∈ valBall K N, f (x + h) = f x) {y : K}
    (hy : y ∉ valBall K (addCharConductor ψ - N)) : localFourier μ ψ f y = 0 := by
  rw [← isTrivialOn_mulShift_iff_mem hψ hψ1] at hy
  obtain ⟨h, hh, hne⟩ : ∃ h ∈ valBall K N, ψ (y * h) ≠ 1 := by
    simpa [IsTrivialOn, AddChar.mulShift_apply] using hy
  have key : localFourier μ ψ f y = (ψ (h * y) : ℂ) * localFourier μ ψ f y :=
    calc ∫ x, f x * (ψ (x * y) : ℂ) ∂μ = ∫ x, f (h + x) * (ψ ((h + x) * y) : ℂ) ∂μ :=
          (integral_add_left_eq_self (fun x => f x * (ψ (x * y) : ℂ)) h).symm
      _ = ∫ x, (ψ (h * y) : ℂ) * (f x * (ψ (x * y) : ℂ)) ∂μ := by
          congr 1
          ext x
          rw [add_comm h x, hfN x h hh, add_mul, AddChar.map_add_eq_mul, Circle.coe_mul]
          ring
      _ = (ψ (h * y) : ℂ) * localFourier μ ψ f y := integral_const_mul _ _
  refine eq_zero_of_eq_mul_of_ne_one (fun h' => hne ?_) key
  rw [mul_comm]
  exact Circle.coe_eq_one.mp h'
end GroundTheory.LocalField
