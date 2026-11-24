-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VectorTaylor.vanish_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:28:52.410386+00:00
-- url     : https://prove2.me/submissions/5cec714c-b7a7-4b34-b66c-f654b48f6df7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticOrthogonalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VectorTaylor
open Filter Topology
namespace GlobalTheory.CompanionTheory.VectorTaylor
theorem _root_.solution (f : ℕ → ℝ → ℂ) (B D : ℝ) (hB : 0 ≤ B) (hD : 1 ≤ D)
    (hd : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t)
    (hb : ∀ k t, ‖f k t‖ ≤ B * D ^ k * (k.factorial : ℝ)) (h0 : ∀ k, f k 0 = 0) (m : ℕ) :
    ∀ t : ℝ, |t| ≤ m * (1 / (4 * D)) → ∀ k, f k t = 0 := by
  have hδ : 0 < 1 / (4 * D) := by positivity
  induction m with
  | zero =>
    intro t ht k
    have htz : t = 0 := by
      have : |t| ≤ 0 := by simpa using ht
      exact abs_nonpos_iff.mp this
    rw [htz]
    exact h0 k
  | succ m ih =>
    intro t ht k
    have hm : (0 : ℝ) < m + 1 := by positivity
    push_cast at ht
    have ht0 : |(m : ℝ) / (m + 1) * t| ≤ m * (1 / (4 * D)) := by
      rw [abs_mul, abs_of_nonneg (by positivity), div_mul_eq_mul_div, div_le_iff₀ hm]
      have := mul_le_mul_of_nonneg_left ht (by positivity : (0 : ℝ) ≤ m)
      linarith
    have hs : |t - (m : ℝ) / (m + 1) * t| ≤ 1 / (4 * D) := by
      have he : t - (m : ℝ) / (m + 1) * t = t / (m + 1) := by
        field_simp
        ring
      rw [he, abs_div, abs_of_pos hm, div_le_iff₀ hm]
      linarith
    have h := step f B D hB hD hd hb _ (ih _ ht0) _ hs k
    simpa using h
end GlobalTheory.CompanionTheory.VectorTaylor
