-- Prove2me | solution 1 for GroundTheory.LocalField.localFourier_localFourier
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:59:49.55763+00:00
-- url     : https://prove2.me/submissions/36bda752-f83f-490e-947d-12474007a692

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierChar
import Definitions.Def_GroundTheory_LocalFields_LocalFourierSchwartz
import Theorems.Thm_GroundTheory_LocalField_exists_invariant_of_mem_schwartzBruhat
import Theorems.Thm_GroundTheory_LocalField_integral_valBall_char
import Theorems.Thm_GroundTheory_LocalField_integrable_of_mem_schwartzBruhat
import Theorems.Thm_GroundTheory_LocalField_localFourier_eq_zero_of_notMem
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_measurableSet_valBall
import Theorems.Thm_GroundTheory_LocalField_measureReal_valBall
import Theorems.Thm_GroundTheory_LocalField_modulus_eq_zero
import Theorems.Thm_GroundTheory_LocalField_modulus_one
import Theorems.Thm_GroundTheory_LocalField_modulus_zero
import Theorems.Thm_GroundTheory_LocalField_residueAlgEquiv_residue
import Theorems.Thm_GroundTheory_LocalField_residueCard_ne_zero
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
theorem _root_.solution {f : K → ℂ} (hf : f ∈ schwartzBruhat K) (z : K) :
    localFourier μ ψ (localFourier μ ψ f) z =
      (((residueCard K : ℝ) ^ (-addCharConductor ψ) * μ.real (valBall K 0) ^ 2 : ℝ) : ℂ) * f (-z) := by
  obtain ⟨N, M, hN, hM⟩ := exists_invariant_of_mem_schwartzBruhat hf
  have hfi : Integrable f μ := integrable_of_mem_schwartzBruhat μ hf
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  let B : Set K := valBall K (addCharConductor ψ - N)
  have hBm : MeasurableSet B := measurableSet_valBall _
  have : IsFiniteMeasure (μ.restrict B) :=
    isFiniteMeasure_restrict.mpr (isCompact_valBall _).measure_lt_top.ne

  have hA : localFourier μ ψ (localFourier μ ψ f) z =
      ∫ y in B, localFourier μ ψ f y * (ψ (y * z) : ℂ) ∂μ := by
    rw [show localFourier μ ψ (localFourier μ ψ f) z =
      ∫ y, localFourier μ ψ f y * (ψ (y * z) : ℂ) ∂μ from rfl]
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      rw [localFourier_eq_zero_of_notMem μ hψ hψ1 hN hy, zero_mul]).symm

  let G : K → K → ℂ := fun y x => f x * (ψ (x * y) : ℂ) * (ψ (y * z) : ℂ)
  have hG : Integrable (Function.uncurry G) ((μ.restrict B).prod μ) := by
    have hdom : Integrable (fun p : K × K => (1 : ℝ) * ‖f p.2‖) ((μ.restrict B).prod μ) :=
      (integrable_const (1 : ℝ)).mul_prod hfi.norm
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hf.1.continuous.comp continuous_snd).mul
        (hψc.comp (continuous_snd.mul continuous_fst))).mul
        (hψc.comp (continuous_fst.mul continuous_const))
    · simp [G, Function.uncurry, Circle.norm_coe]
  have hB : ∫ y in B, localFourier μ ψ f y * (ψ (y * z) : ℂ) ∂μ =
      ∫ y in B, ∫ x, G y x ∂μ ∂μ := by
    congr 1
    ext y
    exact (integral_mul_const _ _).symm

  have hinner : ∀ x, ∫ y in B, G y x ∂μ =
      (valBall K N : Set K).indicator (fun _ => f (-z) * (μ.real B : ℂ)) (x + z) := by
    intro x
    have e : ∀ y, G y x = f x * ((ψ.mulShift (x + z)) y : ℂ) := fun y => by
      simp only [G, AddChar.mulShift_apply]
      rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3
      ring
    simp only [e]
    rw [integral_const_mul, integral_valBall_char]
    by_cases hxz : x + z ∈ valBall K N
    · have ht : IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - N) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_pos ht, Set.indicator_of_mem (show x + z ∈ (valBall K N : Set K) from hxz)]
      have : f x = f (-z) := by
        have := hN (-z) (x + z) hxz
        rw [show -z + (x + z) = x by ring] at this
        exact this
      rw [this]
    · have ht : ¬ IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - N) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_neg ht, Set.indicator_of_notMem (show x + z ∉ (valBall K N : Set K) from hxz),
        mul_zero]
  rw [hA, hB, integral_integral_swap hG]
  simp only [hinner]
  have hpre : ∫ x, (valBall K N : Set K).indicator (fun _ => f (-z) * (μ.real B : ℂ)) (x + z) ∂μ =
      ∫ x, (valBall K N : Set K).indicator (fun _ => f (-z) * (μ.real B : ℂ)) x ∂μ :=
    integral_add_right_eq_self (fun x => (valBall K N : Set K).indicator
      (fun _ => f (-z) * (μ.real B : ℂ)) x) z
  rw [hpre, integral_indicator_const _ (measurableSet_valBall N), Complex.real_smul]
  simp only [B]
  rw [measureReal_valBall μ N, measureReal_valBall μ (addCharConductor ψ - N)]
  have hq : (residueCard K : ℝ) ≠ 0 := by exact_mod_cast residueCard_ne_zero
  have : (residueCard K : ℝ) ^ (-addCharConductor ψ) =
      (residueCard K : ℝ) ^ (-N) * (residueCard K : ℝ) ^ (-(addCharConductor ψ - N)) := by
    rw [← zpow_add₀ hq]
    ring_nf
  rw [this]
  push_cast
  ring
end GroundTheory.LocalField
