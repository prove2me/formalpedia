-- Prove2me | solution 1 for GlobalTheory.GoodHeight.exists_bound_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:42:18.192993+00:00
-- url     : https://prove2.me/submissions/a57c9530-9d4f-4651-8b39-5f66c3d17a63

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsMore
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsBoundRight
import Theorems.Thm_GlobalTheory_LLeft_norm_term_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GoodHeight
namespace GlobalTheory.GoodHeight
theorem _root_.solution : ∃ B : ℝ, 0 ≤ B ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (s : ℂ), 2 ≤ s.re → ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ B := by
  refine ⟨∑' n, ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro N _ χ s hs
  have hs1 : 1 < s.re := by linarith
  have hsum2 : Summable (fun n => ‖LSeries.term (fun n => (Λ n : ℂ)) 2 n‖) :=
    summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by norm_num))
  have key := LSeries_twist_vonMangoldt_eq χ hs1
  rw [← LFunction_eq_LSeries χ hs1, ← deriv_LFunction_eq_deriv_LSeries χ hs1] at key
  rw [← neg_neg (deriv (LFunction χ) s / LFunction χ s), ← neg_div, ← key, norm_neg]
  unfold LSeries
  refine (norm_tsum_le_tsum_norm ?_).trans (Summable.tsum_le_tsum (fun n => ?_) ?_ hsum2)
  · exact summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs1)
  · refine (LSeries.norm_term_le_of_re_le_re _ (show (2 : ℂ).re ≤ s.re by simpa using hs) n).trans
      (LSeries.norm_term_le 2 ?_)
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)
  · exact summable_norm_iff.mpr (LSeriesSummable_twist_vonMangoldt χ hs1)
end GlobalTheory.GoodHeight
