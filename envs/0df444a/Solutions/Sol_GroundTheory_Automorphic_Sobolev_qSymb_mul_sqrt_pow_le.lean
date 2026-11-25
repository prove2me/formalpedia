-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.qSymb_mul_sqrt_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:29:19.186878+00:00
-- url     : https://prove2.me/submissions/15fa0a61-17cd-4ed4-9494-a4f16f9fed5a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_qSymb_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_qSymb_mul_le
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
theorem _root_.solution {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (ξ : E) :
    ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m ≤ 2 ^ m * (cl⁻¹ + Cu) := by
  have hq0 := norm_nonneg (qSymb c w μ ξ)
  rcases le_or_gt 1 ‖ξ‖ with h | h
  · have hS := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le_two_mul h) m
    have hξm : 0 < ‖ξ‖ ^ m := pow_pos (by linarith) m
    have hp : ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖ / cl := by rw [le_div_iff₀ hcl, mul_comm]; exact hlow ξ
    calc ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m ≤ ‖qSymb c w μ ξ‖ * (2 * ‖ξ‖) ^ m := by
          gcongr
      _ = 2 ^ m * (‖qSymb c w μ ξ‖ * ‖ξ‖ ^ m) := by rw [mul_pow]; ring
      _ ≤ 2 ^ m * (‖qSymb c w μ ξ‖ * (‖symb0 c w ξ‖ / cl)) := by gcongr
      _ = 2 ^ m * ((‖qSymb c w μ ξ‖ * ‖symb0 c w ξ‖) * cl⁻¹) := by ring
      _ ≤ 2 ^ m * (1 * cl⁻¹) := by
          gcongr; exact norm_qSymb_mul_le c w hμ0 ξ
      _ ≤ 2 ^ m * (cl⁻¹ + Cu) := by gcongr; linarith
  · have hS := pow_le_pow_left₀ (Real.sqrt_nonneg _) (sqrt_one_add_norm_sq_le_two h.le) m
    have hξm : ‖ξ‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg _) h.le
    have hq : ‖qSymb c w μ ξ‖ ≤ Cu := by
      calc ‖qSymb c w μ ξ‖ ≤ μ * ‖symb0 c w ξ‖ := norm_qSymb_le c w hμ0 ξ
        _ ≤ 1 * (Cu * ‖ξ‖ ^ m) := by gcongr; exact hup ξ
        _ ≤ 1 * (Cu * 1) := by gcongr
        _ = Cu := by ring
    calc ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m ≤ Cu * 2 ^ m := by gcongr
      _ ≤ 2 ^ m * (cl⁻¹ + Cu) := by
          rw [mul_comm]; gcongr; linarith [inv_pos.2 hcl]
end GroundTheory.Automorphic.Sobolev
