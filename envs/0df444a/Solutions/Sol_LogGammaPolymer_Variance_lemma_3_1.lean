-- Prove2me | solution 1 for LogGammaPolymer.Variance.lemma_3_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T15:07:40.325992+00:00
-- url     : https://prove2.me/submissions/76d27b11-554f-484e-9fa5-8870964dda5c

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace Aux_LogGammaPolymer_Variance_lemma_3_1
open LogGammaPolymer.Variance

theorem U_i0 (Y : ℕ × ℕ → ℝ) (i : ℕ) : U Y (i + 1) 0 = Y (i + 1, 0) := by
  unfold U; rw [UV]

theorem V_0j (Y : ℕ × ℕ → ℝ) (j : ℕ) : V Y 0 (j + 1) = Y (0, j + 1) := by
  unfold V; rw [UV]

theorem U_ss (Y : ℕ × ℕ → ℝ) (i j : ℕ) :
    U Y (i + 1) (j + 1) = Y (i + 1, j + 1) * (1 + U Y (i + 1) j / V Y i (j + 1)) := by
  unfold U V; rw [UV]

theorem V_ss (Y : ℕ × ℕ → ℝ) (i j : ℕ) :
    V Y (i + 1) (j + 1) = Y (i + 1, j + 1) * (1 + V Y i (j + 1) / U Y (i + 1) j) := by
  unfold U V; rw [UV]

end Aux_LogGammaPolymer_Variance_lemma_3_1

open LogGammaPolymer.Variance Aux_LogGammaPolymer_Variance_lemma_3_1 in
theorem solution (Y Yt : ℕ × ℕ → ℝ)
    (hY : ∀ p : ℕ × ℕ, p ≠ (0, 0) → 0 < Y p) (hYt : ∀ p : ℕ × ℕ, p ≠ (0, 0) → 0 < Yt p)
    (hU : ∀ i : ℕ, 1 ≤ i → Yt (i, 0) ≤ Y (i, 0))
    (hV : ∀ j : ℕ, 1 ≤ j → Y (0, j) ≤ Yt (0, j))
    (hbulk : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → Y (i, j) = Yt (i, j)) :
    ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → U Yt i j ≤ U Y i j ∧ V Y i j ≤ V Yt i j := by
  have main : ∀ s i j, i + j ≤ s →
      (1 ≤ i → 0 < U Yt i j ∧ U Yt i j ≤ U Y i j) ∧
      (1 ≤ j → 0 < V Y i j ∧ V Y i j ≤ V Yt i j) := by
    intro s
    induction s with
    | zero =>
      intro i j h
      exact ⟨fun hi => by omega, fun hj => by omega⟩
    | succ s ih =>
      intro i j h
      refine ⟨fun hi => ?_, fun hj => ?_⟩
      · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        cases j with
        | zero =>
          rw [U_i0, U_i0]
          exact ⟨hYt _ (by simp), hU _ (by omega)⟩
        | succ j' =>
          obtain ⟨hu0, hu⟩ := (ih (i' + 1) j' (by omega)).1 (by omega)
          obtain ⟨hv0, hv⟩ := (ih i' (j' + 1) (by omega)).2 (by omega)
          rw [U_ss, U_ss, ← hbulk _ _ (by omega) (by omega)]
          have hy := hY (i' + 1, j' + 1) (by simp)
          have hvt : 0 < V Yt i' (j' + 1) := lt_of_lt_of_le hv0 hv
          refine ⟨mul_pos hy (by positivity), ?_⟩
          refine mul_le_mul_of_nonneg_left ?_ hy.le
          have := div_le_div₀ (lt_of_lt_of_le hu0 hu).le hu hv0 hv
          linarith
      · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        cases i with
        | zero =>
          rw [V_0j, V_0j]
          exact ⟨hY _ (by simp), hV _ (by omega)⟩
        | succ i' =>
          obtain ⟨hu0, hu⟩ := (ih (i' + 1) j' (by omega)).1 (by omega)
          obtain ⟨hv0, hv⟩ := (ih i' (j' + 1) (by omega)).2 (by omega)
          rw [V_ss, V_ss, ← hbulk _ _ (by omega) (by omega)]
          have hy := hY (i' + 1, j' + 1) (by simp)
          have huY : 0 < U Y (i' + 1) j' := lt_of_lt_of_le hu0 hu
          refine ⟨mul_pos hy (by positivity), ?_⟩
          refine mul_le_mul_of_nonneg_left ?_ hy.le
          have := div_le_div₀ (lt_of_lt_of_le hv0 hv).le hv hu0 hu
          linarith
  intro i j hi hj
  exact ⟨((main (i + j) i j le_rfl).1 hi).2, ((main (i + j) i j le_rfl).2 hj).2⟩
