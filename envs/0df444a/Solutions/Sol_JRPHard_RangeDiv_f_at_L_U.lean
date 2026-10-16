-- Prove2me | solution 1 for JRPHard.RangeDiv.f_at_L_U
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T06:49:51.33943+00:00
-- url     : https://prove2.me/submissions/a92ccadb-529b-4af8-8445-b6ec9553ef99

import Mathlib
import Definitions.Def_JRPHard_RangeDiv_Setting
open JRPHard.RangeDiv
set_option autoImplicit false

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Mathematical source: Schulz and Telha, arXiv:2007.09045v1, proof of Lemma 3.
theorem solution (M L U : ℕ) (hI : IsRangeDivisorInstance M L U) :
    (∀ q : ℕ, 0 < q → fConv L U q ≤ obj5 M L U q) ∧
    fConv L U L = L + U ∧ fConv L U U = L + U ∧
    (∀ x : ℝ, 0 < x → fConv L U (Real.sqrt ((L : ℝ) * U)) ≤ fConv L U x) := by
  have hL : 0 < (L : ℝ) := by exact_mod_cast hI.1
  have hU : 0 < (U : ℝ) := by exact_mod_cast lt_of_lt_of_le hI.1 hI.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    have hg : 0 < (Nat.gcd q M : ℝ) := by exact_mod_cast Nat.gcd_pos_of_pos_left M hq
    have hgq : (Nat.gcd q M : ℝ) ≤ q := by exact_mod_cast Nat.gcd_le_left M hq
    unfold fConv obj5
    exact add_le_add (div_le_div_of_nonneg_left (by positivity) hg hgq) le_rfl
  · unfold fConv
    push_cast
    field_simp
    ring
  · unfold fConv
    push_cast
    field_simp
  · intro x hx
    have hs : 0 < Real.sqrt ((L : ℝ) * U) := Real.sqrt_pos.2 (mul_pos hL hU)
    have hs2 : Real.sqrt ((L : ℝ) * U)^2 = (L : ℝ) * U := Real.sq_sqrt (by positivity)
    have he : (L : ℝ) * U / Real.sqrt ((L : ℝ) * U) = Real.sqrt ((L : ℝ) * U) := by
      apply (div_eq_iff (ne_of_gt hs)).2
      nlinarith
    simp only [fConv, Nat.cast_mul, he]
    apply (mul_le_mul_iff_left₀ hx).mp
    simp only [add_mul, div_mul_cancel₀ _ (ne_of_gt hx)]
    nlinarith [sq_nonneg (x - Real.sqrt ((L : ℝ) * U))]
