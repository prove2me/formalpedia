-- Prove2me | solution 1 for NewsBundling.Unilateral.lemma2_attention
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:34:03.956024+00:00
-- url     : https://prove2.me/submissions/9b55c33e-8d69-442b-a05c-038d67cd32a7

import Mathlib
import Definitions.Def_NewsBundling_Unilateral_Setting

set_option autoImplicit false
open NewsBundling.Unilateral

theorem solution :
    ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ lam : ℝ, 0 ≤ lam → lam < 1 →
      ∀ T1 : ℝ, IsConsumerBR q lam T1 ↔
        T1 = max ((q - lam) / (1 - lam)) 0 := by
  intro q hq lam hlam0 hlam1 T1
  have hk : 0 < 1 - lam := by linarith
  set T0 := max ((q - lam) / (1 - lam)) 0 with hT0
  have hT0_0 : 0 ≤ T0 := le_max_right _ _
  have hT0_1 : T0 ≤ 1 := by
    apply max_le _ zero_le_one
    rw [div_le_one hk]; linarith [hq.2]
  -- payoff difference formula
  have hdiff : ∀ T T' : ℝ, consumerPayoff q lam T - consumerPayoff q lam T' =
      (1 - lam) * (T - T') * (q - ((lam + (1 - lam) * T) + (lam + (1 - lam) * T')) / 2) := by
    intro T T'
    unfold consumerPayoff utility
    ring
  have hstrict : ∀ T ∈ Set.Icc (0 : ℝ) 1, T ≠ T0 → consumerPayoff q lam T < consumerPayoff q lam T0 := by
    intro T hT hne
    have hd := hdiff T T0
    rcases le_or_gt ((q - lam) / (1 - lam)) 0 with h | h
    · have hT0e : T0 = 0 := by rw [hT0]; exact max_eq_right h
      have hq' : q - lam ≤ 0 := by
        have := (div_nonpos_iff.1 h)
        rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
        · linarith
        · exact h1
      have hTpos : 0 < T := lt_of_le_of_ne hT.1 (fun e => hne (by rw [hT0e]; exact e.symm))
      rw [hT0e] at hd ⊢
      have : (1 - lam) * (T - 0) * (q - ((lam + (1 - lam) * T) + (lam + (1 - lam) * 0)) / 2) < 0 := by
        have h1 : 0 < (1 - lam) * (T - 0) := by nlinarith
        have h2 : q - ((lam + (1 - lam) * T) + (lam + (1 - lam) * 0)) / 2 < 0 := by nlinarith
        exact mul_neg_of_pos_of_neg h1 h2
      linarith
    · have hT0e : T0 = (q - lam) / (1 - lam) := by rw [hT0]; exact max_eq_left h.le
      have hx0 : lam + (1 - lam) * T0 = q := by rw [hT0e]; field_simp; ring
      rw [hx0] at hd
      have hne' : T - T0 ≠ 0 := sub_ne_zero.2 hne
      have : (1 - lam) * (T - T0) * (q - ((lam + (1 - lam) * T) + q) / 2) =
          -((1 - lam) ^ 2 * (T - T0) ^ 2 / 2) := by
        have : q = lam + (1 - lam) * T0 := hx0.symm
        rw [this]; ring
      rw [this] at hd
      have : 0 < (1 - lam) ^ 2 * (T - T0) ^ 2 / 2 := by positivity
      linarith
  constructor
  · rintro ⟨hT1, hBR⟩
    by_contra hne
    have h1 := hstrict T1 hT1 hne
    have h2 := hBR T0 ⟨hT0_0, hT0_1⟩
    linarith
  · intro h
    subst h
    refine ⟨⟨hT0_0, hT0_1⟩, ?_⟩
    intro T hT
    by_cases e : T = T0
    · rw [e]
    · exact (hstrict T hT e).le
