-- Prove2me | solution 1 for HomotopyProxVM.eq_65
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:25:35.456204+00:00
-- url     : https://prove2.me/submissions/b358844b-1c3b-4b4c-840e-4715833425e5

import Definitions.Def_HomotopyProxVM_sigmaConst
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open HomotopyProxVM

theorem solution {τ₀ ω a b : ℝ} (hτ₀ : τ₀ ∈ Set.Ioo (0 : ℝ) 1) (hω : ω ∈ Set.Ioo (0 : ℝ) 1)
    (ha : 0 < a) (hb : 0 < b) :
    let σ := sigmaConst τ₀ ω a b
    ω < σ ∧ σ < 1 ∧ (1 - τ₀) * (1 - σ) / τ₀ = (σ - ω) * a / (ω * b) := by
  have hG : 0 < gammaConst a ω b := div_pos ha (mul_pos hω.1 hb)
  have hden : 0 < 1 - τ₀ + τ₀ * gammaConst a ω b := by
    exact add_pos (sub_pos.mpr hτ₀.2) (mul_pos hτ₀.1 hG)
  dsimp only [sigmaConst]
  refine ⟨?_, ?_, ?_⟩
  · apply (lt_div_iff₀ hden).mpr
    nlinarith [mul_pos (sub_pos.mpr hτ₀.2) (sub_pos.mpr hω.2)]
  · apply (div_lt_one hden).mpr
    nlinarith [mul_pos (mul_pos hτ₀.1 hG) (sub_pos.mpr hω.2)]
  · have hΓ : gammaConst a ω b * (ω*b) = a := by
      dsimp only [gammaConst]
      exact div_mul_cancel₀ _ (mul_pos hω.1 hb).ne'
    field_simp [hden.ne', hτ₀.1.ne', hω.1.ne', hb.ne']
    linear_combination τ₀ * (1 - τ₀) * (1 - ω) * hΓ

#print axioms solution
