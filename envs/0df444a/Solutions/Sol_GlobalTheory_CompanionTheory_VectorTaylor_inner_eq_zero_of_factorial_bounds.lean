-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VectorTaylor.inner_eq_zero_of_factorial_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:08.75094+00:00
-- url     : https://prove2.me/submissions/8d2ef559-1b00-4fb3-b6a8-d80d88022966

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AnalyticOrthogonalVanishing
import Theorems.Thm_GlobalTheory_CompanionTheory_VectorTaylor_vanish_of_le

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
theorem _root_.solution (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (F : ℕ → ℝ → H) (M C : ℝ) (u : H)
    (hd : ∀ k t, HasDerivAt (F k) (F (k + 1) t) t)
    (hb : ∀ k t, ‖F k t‖ ≤ M * C ^ k * (k.factorial : ℝ))
    (h0 : ∀ k, inner ℂ u (F k 0) = 0) : ∀ t, inner ℂ u (F 0 t) = 0 := by
  intro t
  have hD : 1 ≤ max |C| 1 := le_max_right _ _
  have hM : 0 ≤ M := by
    have := hb 0 0
    simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one] at this
    exact (norm_nonneg _).trans this
  have hfd : ∀ k t, HasDerivAt (fun t => inner ℂ u (F k t)) (inner ℂ u (F (k + 1) t)) t := by
    intro k t
    have h := ((innerSL ℂ u).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (hd k t)
    simpa [Function.comp_def] using h
  have hfb : ∀ k t, ‖inner ℂ u (F k t)‖ ≤ (‖u‖ * M) * (max |C| 1) ^ k * (k.factorial : ℝ) := by
    intro k t
    have hCk : C ^ k ≤ (max |C| 1) ^ k :=
      (le_abs_self _).trans (by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (le_max_left _ _) k)
    calc ‖inner ℂ u (F k t)‖ ≤ ‖u‖ * ‖F k t‖ := norm_inner_le_norm u (F k t)
      _ ≤ ‖u‖ * (M * C ^ k * k.factorial) := mul_le_mul_of_nonneg_left (hb k t) (norm_nonneg _)
      _ ≤ ‖u‖ * (M * (max |C| 1) ^ k * k.factorial) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCk hM) (Nat.cast_nonneg _))
            (norm_nonneg _)
      _ = (‖u‖ * M) * (max |C| 1) ^ k * k.factorial := by ring
  obtain ⟨m, hm⟩ := exists_nat_ge (|t| * (4 * max |C| 1))
  have ht : |t| ≤ m * (1 / (4 * max |C| 1)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity)]
    exact hm
  exact vanish_of_le (fun k t => inner ℂ u (F k t)) (‖u‖ * M) (max |C| 1) (by positivity) hD hfd hfb
    h0 m t ht 0
end GlobalTheory.CompanionTheory.VectorTaylor
