-- Prove2me | solution 1 for Kyprianou.Ch04.uniformGridSingleAtomLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:16:08.132193+00:00
-- url     : https://prove2.me/submissions/c1019d5a-1681-4f9f-93fe-b19c3c8623d5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
import Theorems.Thm_AvramDividend_Classical_avram_chat24_uniform_cell_approach_left
open MeasureTheory Filter Set Topology
open scoped NNReal Classical
set_option autoImplicit false

/-- Each positive-time atom contributes exactly its strict-left limiting weight. -/
theorem solution (T r : NNReal) (H : NNReal → ℝ)
    (k : ℕ → ℕ) (hk : ∀ n, k n < n+1)
    (hc : ∀ n, T * (k n : NNReal) / ((n+1 : ℕ) : NNReal) < r ∧
      r ≤ T * ((k n+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal))
    (hH : Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n+1),
      if T * (i : NNReal) / ((n+1 : ℕ) : NNReal) < r ∧
        r ≤ T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal)
      then H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) else 0)
      atTop (𝓝 (H r)) := by
  have he (n : ℕ) : (∑ i ∈ Finset.range (n+1),
      if T * (i : NNReal) / ((n+1 : ℕ) : NNReal) < r ∧
        r ≤ T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal)
      then H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) else 0) =
      H (T * (k n : NNReal) / ((n+1 : ℕ) : NNReal)) := by
    rw [Finset.sum_eq_single (k n)]
    · exact if_pos (hc n)
    · intro i hi hne
      apply if_neg
      intro h
      apply hne
      apply AvramDividend.Classical.avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
        r (T / ((n+1 : ℕ) : NNReal)) i (k n)
      · simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h
      · simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hc n
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr (hk n)))
  simp_rw [he]
  exact hH.comp (AvramDividend.Classical.avram_chat24_uniform_cell_approach_left T r k hc)
