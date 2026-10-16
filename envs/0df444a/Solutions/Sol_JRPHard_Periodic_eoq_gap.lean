-- Prove2me | solution 1 for JRPHard.Periodic.eoq_gap
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T07:37:58.194893+00:00
-- url     : https://prove2.me/submissions/89d36f82-e4b4-4280-a4f4-ae48be5b7b65

import Mathlib
import Definitions.Def_JRPHard_Periodic_Setting
open JRPHard.Periodic
set_option autoImplicit false
namespace JRPResearch

theorem item2_gap (M q : ℕ) (hM : 0 < M) (hq : 0 < q) (hne : q ≠ M) :
    2 * (M : ℝ)^2 * (M + 1) + M ≤ JRPHard.Periodic.eoq2 M q := by
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
  have hg : (q : ℝ) ≤ (M + 1) * ((q : ℝ) - M)^2 := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (q : ℝ) + 1 ≤ M := by exact_mod_cast h
      have hs : (1 : ℝ) ≤ ((q : ℝ) - M)^2 := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ (M : ℝ) + 1 by positivity)
      nlinarith
    · have hh : (M : ℝ) + 1 ≤ q := by exact_mod_cast h
      have hd : 0 ≤ (q : ℝ) - M := by linarith
      have hm := mul_nonneg (show 0 ≤ (q : ℝ) - M - 1 by linarith)
        (show 0 ≤ ((M : ℝ) + 1) * ((q : ℝ) - M) + M by positivity)
      nlinarith
  unfold JRPHard.Periodic.eoq2 JRPHard.Aperiodic.eoq JRPHard.Periodic.coefK2 JRPHard.Periodic.coefH2
  push_cast
  apply (mul_le_mul_iff_left₀ hqR).mp
  simp only [add_mul, div_mul_cancel₀ _ (ne_of_gt hqR)]
  have hm := mul_le_mul_of_nonneg_left hg hMR.le
  nlinarith

end JRPResearch

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, Lemma 2.
theorem solution (M : ℕ) (hM : 2 ≤ M) :
    eoq2 M (M + 1) = eoq2 M M + (coefH2 M : ℝ) / ((M : ℝ) + 1) ∧
    eoq2 M (M - 1) = eoq2 M M + (coefH2 M : ℝ) / ((M : ℝ) - 1) ∧
    (M : ℝ) ≤ (coefH2 M : ℝ) / ((M : ℝ) + 1) ∧
    (M : ℝ) ≤ (coefH2 M : ℝ) / ((M : ℝ) - 1) ∧
    ∀ q₂ : ℕ, 0 < q₂ → q₂ ≠ M → eoq2 M M + (M : ℝ) ≤ eoq2 M q₂ := by
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hp : (0 : ℝ) < M := by linarith
  have hm : (0 : ℝ) < (M : ℝ) - 1 := by linarith
  have hf (q : ℕ) : eoq2 M q = (M : ℝ)^3 * (M + 1) / q + M * (M + 1) * q := by
    simp only [eoq2, JRPHard.Aperiodic.eoq, coefK2, coefH2]
    push_cast
    rfl
  have hval : eoq2 M M = 2 * (M : ℝ)^2 * (M + 1) := by
    rw [hf]
    field_simp
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hf, hval]
    simp only [coefH2, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  · rw [hf, hval]
    simp only [coefH2, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_sub (by omega : 1 ≤ M)]
    field_simp
    ring
  · unfold coefH2
    push_cast
    rw [mul_div_cancel_right₀ _ (by linarith : (M : ℝ) + 1 ≠ 0)]
  · unfold coefH2
    push_cast
    apply (le_div_iff₀ hm).2
    nlinarith
  · intro q hq hne
    rw [hval]
    exact JRPResearch.item2_gap M q (by omega) hq hne
