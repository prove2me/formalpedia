-- Prove2me | solution 1 for ModernConvex.LPDuality.infeasibility_certificate
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:04:51.869663+00:00
-- url     : https://prove2.me/submissions/0ad35dfe-59bc-4209-bbd2-56a893ebbc1c

import Mathlib
import Definitions.Def_ModernConvex_LPDuality_AlternativeSystems

open Matrix

open ModernConvex.LPDuality

theorem g69a1_sum_dot {m n : ℕ} (a : Fin m → Fin n → ℝ) (l : Fin m → ℝ) (x : Fin n → ℝ) :
    (∑ i, l i • a i) ⬝ᵥ x = ∑ i, l i * (a i ⬝ᵥ x) := by
  simp only [sum_dotProduct, smul_dotProduct, smul_eq_mul]

theorem solution {m n : ℕ} (ms : ℕ) (hms : ms ≤ m) (a : Fin m → Fin n → ℝ)
    (b : Fin m → ℝ)
    (hT : (∃ l : Fin m → ℝ, SystemTI ms a b l) ∨ (∃ l : Fin m → ℝ, SystemTII a b l)) :
    ¬ ∃ x : Fin n → ℝ, SystemS ms a b x := by
  rintro ⟨x, hx⟩
  have hge : ∀ i, b i ≤ a i ⬝ᵥ x := by
    intro i
    by_cases h : (i : ℕ) < ms
    · exact ((hx i).1 h).le
    · exact (hx i).2 (by omega)
  rcases hT with ⟨l, hl0, hsum, hb, hpos⟩ | ⟨l, hl0, hsum, hb⟩
  · have hz : ∑ i, l i * (a i ⬝ᵥ x) = 0 := by rw [← g69a1_sum_dot, hsum, zero_dotProduct]
    have hdiff : 0 < ∑ i, l i * (a i ⬝ᵥ x - b i) := by
      by_contra hc
      push_neg at hc
      have hall : ∀ i, 0 ≤ l i * (a i ⬝ᵥ x - b i) :=
        fun i => mul_nonneg (hl0 i) (by linarith [hge i])
      have hzero : ∀ i ∈ Finset.univ, l i * (a i ⬝ᵥ x - b i) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hall i)).mp (le_antisymm hc
          (Finset.sum_nonneg fun i _ => hall i))
      have : ∑ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < ms), l i ≤ 0 := by
        apply Finset.sum_nonpos
        intro i hi
        simp only [Finset.mem_filter] at hi
        have h1 := hzero i (Finset.mem_univ _)
        have h2 := (hx i).1 hi.2
        rcases mul_eq_zero.mp h1 with h | h
        · exact h.le
        · linarith
      linarith
    simp only [mul_sub, Finset.sum_sub_distrib] at hdiff
    linarith
  · have hz : ∑ i, l i * (a i ⬝ᵥ x) = 0 := by rw [← g69a1_sum_dot, hsum, zero_dotProduct]
    have : ∑ i, l i * b i ≤ ∑ i, l i * (a i ⬝ᵥ x) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hge i) (hl0 i)
    linarith
