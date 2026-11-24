-- Prove2me | solution 1 for GlobalTheory.WittGaussMul.exists_lt_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:32:54.277867+00:00
-- url     : https://prove2.me/submissions/f5ede1f2-c703-48d4-bd29-e860a099b398

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormUltrametricStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WittVectorGaussNormMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open GlobalTheory.WittGaussMul
namespace GlobalTheory.WittGaussMul
theorem _root_.solution (f : ℕ → ℝ) (B : ℝ) (hB : 0 < B) (i : ℕ) (h : ∀ k < i, f k < B) :
    ∃ c, 0 ≤ c ∧ c < B ∧ ∀ k < i, f k ≤ c := by
  induction i with
  | zero => exact ⟨0, le_rfl, hB, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ i ih =>
    obtain ⟨c, hc0, hcB, hc⟩ := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    refine ⟨max c (f i), le_max_of_le_left hc0, max_lt hcB (h i (Nat.lt_succ_self i)), ?_⟩
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact le_max_of_le_left (hc k hk)
    · exact le_max_right _ _
end GlobalTheory.WittGaussMul
