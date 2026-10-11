-- Prove2me | solution 1 for GreshamLaw.thiers_law
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:16:30.523985+00:00
-- url     : https://prove2.me/submissions/047e14ae-28af-4900-9390-e35a0e601f94

import Mathlib
import Definitions.Def_GreshamLaw_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open GreshamLaw

theorem solution {ι : Type*} [DecidableEq ι] (coin : ι → Coin)
    (s good bad : Finset ι) (hpart : good ∪ bad = s)
    (p ε : ℝ) (hp : 0 < p)
    (hworthless : ∀ b ∈ bad, (coin b).melt ≤ ε)
    (hsmall : (bad.card : ℝ) * ε < p)
    (P : Finset ι) (hPs : P ⊆ s)
    (hacc : AcceptsAtMarketValue coin P p) :
    (P ∩ good).Nonempty := by
  by_contra hnone
  have hPbad : P ⊆ bad := by
    intro i hi
    have his : i ∈ s := hPs hi
    rw [← hpart, Finset.mem_union] at his
    rcases his with hig | hib
    · exact False.elim (hnone ⟨i, Finset.mem_inter.mpr ⟨hi, hig⟩⟩)
    · exact hib
  have hsum : totalMelt coin P ≤ (P.card : ℝ) * ε := by
    unfold totalMelt
    calc
      (∑ i ∈ P, (coin i).melt) ≤ ∑ i ∈ P, ε := by
        apply Finset.sum_le_sum
        intro i hi
        exact hworthless i (hPbad hi)
      _ = (P.card : ℝ) * ε := by simp
  have hcard : (P.card : ℝ) ≤ (bad.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card hPbad)
  change p ≤ totalMelt coin P at hacc
  by_cases hε : 0 ≤ ε
  · have hm := mul_le_mul_of_nonneg_right hcard hε
    linarith
  · have hneg : ε ≤ 0 := le_of_lt (lt_of_not_ge hε)
    have hm : (P.card : ℝ) * ε ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hneg
    linarith
