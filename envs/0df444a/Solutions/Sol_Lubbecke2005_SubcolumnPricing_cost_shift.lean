-- Prove2me | solution 1 for Lubbecke2005.SubcolumnPricing.cost_shift
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:45:41.258745+00:00
-- url     : https://prove2.me/submissions/2215016c-b3db-473b-8c71-8aab628750dd

import Mathlib
import Definitions.Def_Lubbecke2005_SubcolumnPricing_Columns
open Lubbecke2005.SubcolumnPricing

private theorem incidence_sum {m : ℕ} (s : Finset (Fin m)) :
    (∑ i, incidence s i) = (s.card : ℝ) := by
  simp [incidence]

theorem solution {m : ℕ} (𝒜 : Finset (Finset (Fin m))) (c : Finset (Fin m) → ℝ)
    (hweak : ∀ r ∈ 𝒜, ∀ s ∈ 𝒜, r ⊂ s → c r ≤ c s) :
    SubcolumnProperty 𝒜 (fun s => c s + (s.card : ℝ)) ∧
    ∀ lam : Finset (Fin m) → ℝ,
      (∑ s ∈ 𝒜, lam s • incidence s) = (1 : Fin m → ℝ) →
      ∑ s ∈ 𝒜, (c s + (s.card : ℝ)) * lam s = ∑ s ∈ 𝒜, c s * lam s + (m : ℝ) := by
  constructor
  · intro r hr s hs hrs
    exact add_lt_add_of_le_of_lt (hweak r hr s hs hrs) (by exact_mod_cast Finset.card_lt_card hrs)
  · intro lam hlam
    have hsum := congrArg (fun v : Fin m → ℝ => ∑ i, v i) hlam
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
    rw [Finset.sum_comm] at hsum
    simp_rw [← Finset.mul_sum, incidence_sum] at hsum
    simp only [add_mul, Finset.sum_add_distrib]
    congr 1
    simpa [mul_comm] using hsum
