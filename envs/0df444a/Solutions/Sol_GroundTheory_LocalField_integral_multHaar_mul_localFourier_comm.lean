-- Prove2me | solution 1 for GroundTheory.LocalField.integral_multHaar_mul_localFourier_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:29.669571+00:00
-- url     : https://prove2.me/submissions/f339addd-a62f-493f-b559-b5d7e212c5af

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral
import Definitions.Def_GroundTheory_LocalFields_LocalZetaTate
import Theorems.Thm_GroundTheory_LocalField_integral_mul_localFourier_comm
import Theorems.Thm_GroundTheory_LocalField_integral_multHaar_mul_modulus
import Theorems.Thm_GroundTheory_LocalField_coe_valBall_zero
import Theorems.Thm_GroundTheory_LocalField_eq_smul_haarIntegers
import Theorems.Thm_GroundTheory_LocalField_isOpen_valBall


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]
variable (μ : Measure K) [μ.IsAddHaarMeasure] {ψ : AddChar K Circle} (hψ : Continuous ψ)
include hψ
namespace GroundTheory.LocalField
theorem _root_.solution {f g : K → ℂ} (hf : f ∈ schwartzBruhat K)
    (hg : g ∈ schwartzBruhat K) (y : K) :
    ∫ u, f u * localFourier μ ψ g ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K =
      ∫ u, g u * localFourier μ ψ f ((u : K) * y) * ((modulus (u : K) : ℝ) : ℂ) ∂multHaar K := by
  rw [integral_multHaar_mul_modulus (fun x => f x * localFourier μ ψ g (x * y)),
    integral_multHaar_mul_modulus (fun x => g x * localFourier μ ψ f (x * y))]
  congr 1
  have hμ := eq_smul_haarIntegers μ
  have key := integral_mul_localFourier_comm μ hψ hf hg y
  have hc : (μ (𝒪[K] : Set K)).toReal ≠ 0 := by
    refine ENNReal.toReal_ne_zero.mpr ⟨?_, ?_⟩
    · rw [← coe_valBall_zero]
      exact ((isOpen_valBall 0).measure_pos μ ⟨0, zero_mem _⟩).ne'
    · rw [← coe_valBall_zero]
      exact (isCompact_valBall 0).measure_lt_top.ne
  have hJ : ∀ F : K → ℂ, ∫ x, F x ∂μ = ((μ (𝒪[K] : Set K)).toReal : ℂ) * ∫ x, F x ∂haarIntegers K :=
    fun F => by
      conv_lhs => rw [hμ]
      rw [integral_smul_measure, Complex.real_smul]
  rw [hJ, hJ] at key
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hc) key
end GroundTheory.LocalField
