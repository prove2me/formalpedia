-- Prove2me | solution 1 for MultiPriceOnline.Hardness.lemma_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T21:05:22.04182+00:00
-- url     : https://prove2.me/submissions/2be19b4a-dbf5-49bc-abdb-e27af2ac06c4

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet

open Finset

open MultiPriceOnline.Hardness in
theorem solution {m : ℕ} {r α B : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (j : ℕ) (hj1 : 1 ≤ j) (hjm : j ≤ m) (τ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hrep : ∀ l : ℕ, j ≤ l → l ≤ m → (Asum m α j - τ) / ((m : ℝ) - j + 1) ≤ α l) :
    IsGreatest
      {v : ℝ | ∃ lam : ℕ → ℝ, (∀ l ∈ Icc j m, 0 ≤ lam l) ∧ (∑ l ∈ Icc j m, lam l) ≤ τ ∧
        v = ∑ l ∈ Icc j m, r l * B l * n * (1 - Real.exp (-lam l)) * k}
      ((n : ℝ) * k * ∑ l ∈ Icc j m,
        r l * B l * (1 - Real.exp (-α l + (Asum m α j - τ) / ((m : ℝ) - j + 1)))) := by
  set c := (Asum m α j - τ) / ((m : ℝ) - j + 1) with hc
  have hden : (0 : ℝ) < (m : ℝ) - j + 1 := by
    have : (j : ℝ) ≤ m := by exact_mod_cast hjm
    linarith
  set K := Real.exp c * (r 1 * Real.exp (-α 1)) with hK
  have hKpos : 0 < K := by
    have := hr.1
    positivity
  have hconst : ∀ l ∈ Icc j m, r l * B l * Real.exp (-(α l - c)) = K := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    have e : r l * B l * Real.exp (-(α l - c)) = Real.exp c * (B l * r l * Real.exp (-α l)) := by
      rw [show -(α l - c) = -α l + c by ring, Real.exp_add]; ring
    rw [e, hK]
    congr 1
    by_cases h1 : l = 1
    · subst h1; rw [hB.1]; ring
    · exact hB.2 l (by omega) hl.2
  have hcard : ∑ l ∈ Icc j m, c = ((m : ℝ) - j + 1) * c := by
    rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
    congr 1
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hAsum : Asum m α j = ∑ l ∈ Icc j m, α l := rfl
  constructor
  · refine ⟨fun l => α l - c, fun l hl => ?_, ?_, ?_⟩
    · rw [Finset.mem_Icc] at hl
      have := hrep l hl.1 hl.2
      simp only
      linarith
    · rw [Finset.sum_sub_distrib, hcard, ← hAsum, hc]
      field_simp
      linarith
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [show -(α l - c) = -α l + c by ring]
      ring
  · rintro v ⟨lam, hlam0, hlamsum, rfl⟩
    have htan : ∀ l ∈ Icc j m, r l * B l * (1 - Real.exp (-lam l)) ≤
        r l * B l * (1 - Real.exp (-(α l - c))) + K * (lam l - (α l - c)) := by
      intro l hl
      have hK' := hconst l hl
      have hpos : 0 < r l * B l := by
        by_contra hneg
        push_neg at hneg
        have : r l * B l * Real.exp (-(α l - c)) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hneg (Real.exp_pos _).le
        linarith
      have hexp : Real.exp (-(α l - c)) * (1 - (lam l - (α l - c))) ≤ Real.exp (-lam l) := by
        have h1 := Real.add_one_le_exp ((α l - c) - lam l)
        have h2 : Real.exp (-lam l) = Real.exp (-(α l - c)) * Real.exp ((α l - c) - lam l) := by
          rw [← Real.exp_add]; ring_nf
        rw [h2]
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith
      have := mul_le_mul_of_nonneg_left hexp hpos.le
      rw [← hK']
      nlinarith
    have hsum : ∑ l ∈ Icc j m, r l * B l * (1 - Real.exp (-lam l)) ≤
        ∑ l ∈ Icc j m, r l * B l * (1 - Real.exp (-α l + c)) := by
      calc ∑ l ∈ Icc j m, r l * B l * (1 - Real.exp (-lam l))
          ≤ ∑ l ∈ Icc j m, (r l * B l * (1 - Real.exp (-(α l - c))) + K * (lam l - (α l - c))) :=
            Finset.sum_le_sum htan
        _ = ∑ l ∈ Icc j m, r l * B l * (1 - Real.exp (-α l + c)) +
              K * (∑ l ∈ Icc j m, lam l - τ) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
              Finset.sum_sub_distrib, hcard, ← hAsum]
            have : ((m : ℝ) - j + 1) * c = Asum m α j - τ := by
              rw [hc]; field_simp
            rw [this]
            congr 1
            · apply Finset.sum_congr rfl; intro l _
              rw [show -(α l - c) = -α l + c by ring]
            · ring
        _ ≤ ∑ l ∈ Icc j m, r l * B l * (1 - Real.exp (-α l + c)) := by
            have : K * (∑ l ∈ Icc j m, lam l - τ) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos hKpos.le (by linarith)
            linarith
    have hnk : (0 : ℝ) ≤ (n : ℝ) * k := by positivity
    calc ∑ l ∈ Icc j m, r l * B l * n * (1 - Real.exp (-lam l)) * k
        = (n : ℝ) * k * ∑ l ∈ Icc j m, r l * B l * (1 - Real.exp (-lam l)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro l _; ring
      _ ≤ (n : ℝ) * k * ∑ l ∈ Icc j m, r l * B l * (1 - Real.exp (-α l + c)) :=
          mul_le_mul_of_nonneg_left hsum hnk
