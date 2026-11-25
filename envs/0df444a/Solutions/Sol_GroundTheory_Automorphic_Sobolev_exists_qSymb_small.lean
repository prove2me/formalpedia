-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.exists_qSymb_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:15:17.177078+00:00
-- url     : https://prove2.me/submissions/0ddc85df-c508-44f6-a1f1-1ddb18668149

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_one_le_sqrt_one_add_norm_sq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_le_sqrt_one_add_norm_sq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_qSymb_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_qSymb_mul_sqrt_pow_le

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
theorem _root_.solution (hm : 1 ≤ m) {ε : ℝ} (hε : 0 < ε) :
    ∃ μ : ℝ, 0 < μ ∧ μ ≤ 1 ∧ ∀ ξ : E, ‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (m - 1) ≤ ε := by
  set CQ := 2 ^ m * (cl⁻¹ + Cu)
  have hCQ : 0 < CQ := by positivity
  set lam := max 1 (2 * CQ / ε)
  have hlam1 : 1 ≤ lam := le_max_left _ _
  set S0 := Real.sqrt (1 + lam ^ 2)
  have hS01 : 1 ≤ S0 := by rw [Real.one_le_sqrt]; nlinarith
  set D := (Cu + 1) * S0 ^ (2 * m)
  have hD : 0 < D := by positivity
  refine ⟨min 1 (ε / (2 * D)), lt_min one_pos (by positivity), min_le_left _ _, fun ξ ↦ ?_⟩
  set μ := min 1 (ε / (2 * D))
  have hμ0 : 0 ≤ μ := le_min zero_le_one (by positivity)
  have hμ1 : μ ≤ 1 := min_le_left _ _
  set S := Real.sqrt (1 + ‖ξ‖ ^ 2)
  have hS1 : 1 ≤ S := one_le_sqrt_one_add_norm_sq ξ
  have hq0 := norm_nonneg (qSymb c w μ ξ)
  rcases le_or_gt lam ‖ξ‖ with h | h
  · have hSl : lam ≤ S := h.trans (norm_le_sqrt_one_add_norm_sq ξ)
    have key := qSymb_mul_sqrt_pow_le c w hcl hCu hlow hup hμ0 hμ1 ξ
    have e : S ^ m = S ^ (m - 1) * S := by rw [← pow_succ, Nat.sub_add_cancel hm]
    have hSpos : 0 < S := by linarith
    have h1 : ‖qSymb c w μ ξ‖ * S ^ (m - 1) ≤ CQ / S := by
      rw [le_div_iff₀ hSpos]
      calc ‖qSymb c w μ ξ‖ * S ^ (m - 1) * S = ‖qSymb c w μ ξ‖ * S ^ m := by rw [e]; ring
        _ ≤ CQ := key
    calc ‖qSymb c w μ ξ‖ * S ^ (m - 1) ≤ CQ / S := h1
      _ ≤ CQ / lam := by gcongr
      _ ≤ CQ / (2 * CQ / ε) := by gcongr; exact le_max_right _ _
      _ = ε / 2 := by field_simp
      _ ≤ ε := by linarith
  · have hSS0 : S ≤ S0 := Real.sqrt_le_sqrt (by nlinarith [norm_nonneg ξ])
    have hξS : ‖ξ‖ ^ m ≤ S ^ m := pow_le_pow_left₀ (norm_nonneg _) (norm_le_sqrt_one_add_norm_sq ξ) m
    have hq : ‖qSymb c w μ ξ‖ ≤ μ * (Cu * S ^ m) := by
      calc ‖qSymb c w μ ξ‖ ≤ μ * ‖symb0 c w ξ‖ := norm_qSymb_le c w hμ0 ξ
        _ ≤ μ * (Cu * ‖ξ‖ ^ m) := by gcongr; exact hup ξ
        _ ≤ μ * (Cu * S ^ m) := by gcongr
    calc ‖qSymb c w μ ξ‖ * S ^ (m - 1) ≤ μ * (Cu * S ^ m) * S ^ (m - 1) := by gcongr
      _ = μ * Cu * S ^ (m + (m - 1)) := by rw [pow_add]; ring
      _ ≤ μ * (Cu + 1) * S0 ^ (2 * m) := by
          gcongr
          · linarith
          · calc S ^ (m + (m - 1)) ≤ S ^ (2 * m) := pow_le_pow_right₀ hS1 (by omega)
              _ ≤ S0 ^ (2 * m) := pow_le_pow_left₀ (by linarith) hSS0 _
      _ = μ * D := by ring
      _ ≤ ε / (2 * D) * D := by gcongr; exact min_le_right _ _
      _ = ε / 2 := by field_simp
      _ ≤ ε := by linarith
end GroundTheory.Automorphic.Sobolev
