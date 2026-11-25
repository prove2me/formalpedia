-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.rhoSymb_mul_sqrt_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:12.968115+00:00
-- url     : https://prove2.me/submissions/2a223d78-26ec-475f-996a-7928cd96fc4b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_rhoSymb
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_rhoSymb_le_one
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sqrt_one_add_norm_sq_le_two_mul
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sqrt_one_add_norm_sq_le_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) {cl Cu : ℝ}
variable (hcl : 0 < cl) (hCu : 0 ≤ Cu) (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖)
  (hup : ∀ ξ, ‖symb0 c w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {μ : ℝ} (hμ : 0 < μ) (ξ : E) :
    ‖rhoSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (2 * m) ≤ 4 ^ m * (1 + (μ * cl ^ 2)⁻¹) := by
  have hr0 := norm_nonneg (rhoSymb c w μ ξ)
  have hK : 4 ^ m ≤ 4 ^ m * (1 + (μ * cl ^ 2)⁻¹) := by
    have : 0 ≤ (μ * cl ^ 2)⁻¹ := by positivity
    nlinarith [pow_pos (by norm_num : (0:ℝ) < 4) m]
  rcases le_or_gt 1 ‖ξ‖ with h | h
  · have hS := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le_two_mul h) (2 * m)
    have hξ : 0 < ‖ξ‖ := by linarith
    have hp2 : (cl * ‖ξ‖ ^ m) ^ 2 ≤ ‖symb0 c w ξ‖ ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hlow ξ) 2
    have hpos : 0 < μ * cl ^ 2 * ‖ξ‖ ^ (2 * m) := by positivity
    have hρ : ‖rhoSymb c w μ ξ‖ ≤ (μ * cl ^ 2 * ‖ξ‖ ^ (2 * m))⁻¹ := by
      rw [norm_rhoSymb c w hμ.le]
      apply inv_anti₀ hpos
      have : μ * cl ^ 2 * ‖ξ‖ ^ (2 * m) = μ * (cl * ‖ξ‖ ^ m) ^ 2 := by ring
      rw [this]; nlinarith
    calc ‖rhoSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (2 * m)
        ≤ (μ * cl ^ 2 * ‖ξ‖ ^ (2 * m))⁻¹ * (2 * ‖ξ‖) ^ (2 * m) := by gcongr
      _ = 4 ^ m * (μ * cl ^ 2)⁻¹ := by
          rw [mul_pow, pow_mul 2 2 m]; field_simp; norm_num
      _ ≤ 4 ^ m * (1 + (μ * cl ^ 2)⁻¹) := by gcongr; linarith
  · have hS := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le_two h.le) (2 * m)
    calc ‖rhoSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (2 * m) ≤ 1 * 2 ^ (2 * m) := by
          gcongr; exact norm_rhoSymb_le_one c w hμ.le ξ
      _ = 4 ^ m := by rw [one_mul, pow_mul]; norm_num
      _ ≤ _ := hK
end GroundTheory.Automorphic.Sobolev
