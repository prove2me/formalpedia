-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.exists_norm_le_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:52.903546+00:00
-- url     : https://prove2.me/submissions/4c3d332c-b418-44fb-928f-800ee0227bec

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_Sobolev
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevDuality
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMollifier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_SobolevSpace_toDistribution_lineDerivCLM
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_dualEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Sobolev.SobolevSpace.toDistribution_lineDerivCLM
attribute [local simp] GroundTheory.Automorphic.Sobolev.dualEquiv_apply



set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution (χ : 𝓢(E, ℂ)) (r : ℝ) :
    ∃ C, ∀ ξ : E, ‖χ ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  set n : ℕ := ⌈-r / 2⌉₊
  refine ⟨2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ), fun ξ ↦ ?_⟩
  have h0 : ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ 0 0 χ := by
    have := SchwartzMap.le_seminorm ℂ 0 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have h1 : ‖ξ‖ ^ (2 * n) * ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ (2 * n) 0 χ := by
    have := SchwartzMap.le_seminorm ℂ (2 * n) 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have hb : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have hpow : (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
    rcases le_total (‖ξ‖ ^ 2) 1 with h | h
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
            have : 0 ≤ (‖ξ‖ ^ 2) ^ n := by positivity
            nlinarith [pow_pos (two_pos (α := ℝ)) n]
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ (2 * ‖ξ‖ ^ 2) ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ = 2 ^ n * (‖ξ‖ ^ 2) ^ n := by rw [mul_pow]
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by gcongr; linarith
  have key : (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤
      2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) := by
    calc (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) * ‖χ ξ‖ := by gcongr
      _ = 2 ^ n * (‖χ ξ‖ + ‖ξ‖ ^ (2 * n) * ‖χ ξ‖) := by rw [pow_mul]; ring
      _ ≤ _ := by gcongr
  have hpos : 0 < (1 + ‖ξ‖ ^ 2) ^ n := by positivity
  have hexp : (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hb
    have := Nat.le_ceil (-r / 2)
    linarith
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast] at hexp
  calc ‖χ ξ‖ = ((1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖) * ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by
        field_simp
    _ ≤ 2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) *
        ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by gcongr
    _ ≤ _ := by
        gcongr
end GroundTheory.Automorphic.Sobolev
