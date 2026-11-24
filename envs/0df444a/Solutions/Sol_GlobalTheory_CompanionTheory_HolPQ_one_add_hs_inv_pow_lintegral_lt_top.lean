-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HolPQ.one_add_hs_inv_pow_lintegral_lt_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:57:36.056428+00:00
-- url     : https://prove2.me/submissions/392cfb74-a323-4c2f-b838-a69f5ac19d34

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_OneAddHsInvPowLintegralLtTop
import Theorems.Thm_GlobalTheory_CompanionTheory_HolPQ_muG_hs_ball_le
import Theorems.Thm_GlobalTheory_CompanionTheory_HolPQ_continuous_hs_umat
import Theorems.Thm_GlobalTheory_CompanionTheory_HolPQ_lintegral_one_add_inv_pow_lt_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset PI.UpqRep
open scoped InnerProductSpace ENNReal ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolPQ
namespace GlobalTheory.CompanionTheory.HolPQ
theorem _root_.solution : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
    ∫⁻ g, ENNReal.ofReal (((1 + hs (umat g))⁻¹) ^ s) ∂(muG ε) < ⊤ := by
  intro n ε
  obtain ⟨C, hC⟩ := muG_hs_ball_le n ε
  refine ⟨n ^ 2 + 1, fun s hs' => ?_⟩
  refine lintegral_one_add_inv_pow_lt_top (muG ε) (fun g => hs (umat g))
    (continuous_hs_umat ε).measurable (fun g => ?_) (n ^ 2) C (fun k => ?_) s hs'
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  · have e : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    have h1 := hC ((2 : ℝ) ^ k) (one_le_pow₀ (by norm_num))
    have e2 : ((2 : ℝ) ^ k) ^ (2 * n ^ 2) = ((4 : ℝ) ^ k) ^ n ^ 2 := by
      rw [e]; exact pow_mul _ 2 (n ^ 2)
    rw [e2, ← e] at h1
    exact h1
end GlobalTheory.CompanionTheory.HolPQ
