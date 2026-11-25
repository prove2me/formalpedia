-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Analysis.tendsto_factorial_mul_div_pow_of_eps_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:31:43.06641+00:00
-- url     : https://prove2.me/submissions/b90cae58-fb8f-4289-acbe-3a53277bfc8c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TendstoOfAsymptoticBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Analysis
namespace GlobalTheory.CompanionTheory.Analysis
theorem _root_.solution (f : ℕ → ℝ) (G : ℝ) (D : ℕ)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, (G - ε) * (n : ℝ) ^ D / (D.factorial : ℝ) ≤ f n)
    (hu : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, f n ≤ (G + ε) * (n : ℝ) ^ D / (D.factorial : ℝ)) :
    Tendsto (fun n : ℕ => (D.factorial : ℝ) * f n / (n : ℝ) ^ D) atTop (𝓝 G) := by
  have hfac : (0 : ℝ) < (D.factorial : ℝ) := by exact_mod_cast D.factorial_pos
  have hev : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) ^ D := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hl ((G - a) / 2) (by linarith), hev] with n hn hp
    rw [div_le_iff₀ hfac] at hn
    have key : G - (G - a) / 2 ≤ (D.factorial : ℝ) * f n / (n : ℝ) ^ D := by
      rw [le_div_iff₀ hp]
      linarith
    linarith
  · filter_upwards [hu ((b - G) / 2) (by linarith), hev] with n hn hp
    rw [le_div_iff₀ hfac] at hn
    have key : (D.factorial : ℝ) * f n / (n : ℝ) ^ D ≤ G + (b - G) / 2 := by
      rw [div_le_iff₀ hp]
      linarith
    linarith
end GlobalTheory.CompanionTheory.Analysis
