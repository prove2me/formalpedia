-- Prove2me | solution 1 for GlobalTheory.T.count_growth_exponential_radii
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:16:34.056806+00:00
-- url     : https://prove2.me/submissions/5aec2847-c5f9-4b56-81c1-4c117a60d184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountGrowthExponentialRadii
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CountGrowthExponentialRadiiStatement
import Theorems.Thm_GlobalTheory_hsGrowth_exp_radius


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (D e δ : ℕ) (N : ℕ → ℝ → ℕ) (κ t : ℝ), 0 < e → 0 < κ → κ ≤ 1 → 0 < t → (∀ m, ∀ R R' : ℝ, 0 ≤ R → R ≤ R' → N m R ≤ N m R') → (∀ s : ℕ, s < e → ∃ (c c' : ℕ) (C C' : ℝ), 0 < C ∧ 0 < C' ∧ ∀ (q : ℕ) (R : ℝ), 0 ≤ R → (2 * ⌊R⌋₊ + 1) ^ (δ * (q + D).choose D) ≤ N (e * (q + c) + s) (C * (q + D).choose D * R) ∧ N (e * q + s) R ≤ (2 * ⌊C' * R / κ ^ (q + c')⌋₊ + 1) ^ (δ * (q + c' + D).choose D)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, δ / ((e : ℝ) ^ D * D.factorial) * t - ε ≤ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ∧ Real.log (N m (Real.exp (t * m))) / (m : ℝ) ^ (D + 1) ≤ δ / ((e : ℝ) ^ D * D.factorial) * (t - Real.log κ / e) + ε := by
  first | exact @GlobalTheory.hsGrowth_exp_radius | exact GlobalTheory.hsGrowth_exp_radius | (intros; apply GlobalTheory.hsGrowth_exp_radius <;> assumption)
end _root_.GlobalTheory.T
