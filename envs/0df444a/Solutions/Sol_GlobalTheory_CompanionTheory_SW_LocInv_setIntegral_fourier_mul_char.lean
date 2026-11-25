-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.LocInv.setIntegral_fourier_mul_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:36:38.456381+00:00
-- url     : https://prove2.me/submissions/3f43037d-9bff-4918-bdde-f4ab8341186a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
import Theorems.Thm_GroundTheory_LocalField_coe_homeomorphOfIsAlgebraic
import Theorems.Thm_GroundTheory_LocalField_integral_valBall_char
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
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInv
open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
namespace GlobalTheory.CompanionTheory.SW.LocInv
theorem _root_.solution {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ : K → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) (z : K) (k : ℤ) :
    ∫ y in valBall K (addCharConductor ψ - k),
        (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) * (ψ (y * z) : ℂ) ∂(selfDualMeasure ψ) =
      (((selfDualMeasure ψ).real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) *
        ∫ x in valBall K k, Φ (x - z) ∂(selfDualMeasure ψ) := by
  set μ := selfDualMeasure ψ with hμ
  have hfi : Integrable Φ μ := hΦ.integrable_of_hasCompactSupport hc
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have : IsFiniteMeasure (μ.restrict (valBall K (addCharConductor ψ - k))) :=
    isFiniteMeasure_restrict.mpr (isCompact_valBall _).measure_lt_top.ne
  let G : K → K → ℂ := fun y x => Φ x * (ψ (x * y) : ℂ) * (ψ (y * z) : ℂ)
  have hG : Integrable (Function.uncurry G)
      ((μ.restrict (valBall K (addCharConductor ψ - k))).prod μ) := by
    have hdom : Integrable (fun p : K × K => (1 : ℝ) * ‖Φ p.2‖)
        ((μ.restrict (valBall K (addCharConductor ψ - k))).prod μ) :=
      (integrable_const (1 : ℝ)).mul_prod hfi.norm
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hΦ.comp continuous_snd).mul
        (hψc.comp (continuous_snd.mul continuous_fst))).mul
        (hψc.comp (continuous_fst.mul continuous_const))
    · simp [G, Function.uncurry, Circle.norm_coe]
  have hB : ∫ y in valBall K (addCharConductor ψ - k),
        (∫ x, Φ x * (ψ (x * y) : ℂ) ∂μ) * (ψ (y * z) : ℂ) ∂μ =
      ∫ y in valBall K (addCharConductor ψ - k), ∫ x, G y x ∂μ ∂μ := by
    congr 1
    ext y
    exact (integral_mul_const _ _).symm
  have hinner : ∀ x, ∫ y in valBall K (addCharConductor ψ - k), G y x ∂μ =
      (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) (x + z) := by
    intro x
    have e : ∀ y, G y x = Φ x * ((ψ.mulShift (x + z)) y : ℂ) := fun y => by
      simp only [G, AddChar.mulShift_apply]
      rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3
      ring
    simp only [e]
    rw [integral_const_mul, integral_valBall_char]
    by_cases hxz : x + z ∈ valBall K k
    · have ht : IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - k) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_pos ht, Set.indicator_of_mem (show x + z ∈ (valBall K k : Set K) from hxz),
        add_sub_cancel_right, mul_comm]
    · have ht : ¬ IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - k) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_neg ht, Set.indicator_of_notMem (show x + z ∉ (valBall K k : Set K) from hxz),
        mul_zero]
  rw [hB, integral_integral_swap hG]
  simp only [hinner]
  have hpre : ∫ x, (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) (x + z) ∂μ =
      ∫ x, (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) x ∂μ :=
    integral_add_right_eq_self (fun x => (valBall K k : Set K).indicator
      (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) x) z
  rw [hpre, integral_indicator (measurableSet_valBall k), integral_const_mul]
end GlobalTheory.CompanionTheory.SW.LocInv
