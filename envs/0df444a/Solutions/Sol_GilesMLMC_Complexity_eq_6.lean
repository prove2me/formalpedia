-- Prove2me | solution 1 for GilesMLMC.Complexity.eq_6
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T19:42:50.888986+00:00
-- url     : https://prove2.me/submissions/b89d4d5d-b30a-4371-abfc-7d33b6c847f2

import Definitions.Def_GilesMLMC_Complexity_Choices
open GilesMLMC.Complexity

theorem solution
    (M : ℕ) (hM : 2 ≤ M) (T : ℝ) (hT : 0 < T)
    (α c₁ ε : ℝ) (hα : 0 < α) (hc₁ : 0 < c₁) (hε : 0 < ε) :
    (M : ℝ) ^ (-α) * ε / Real.sqrt 2 < c₁ * hz M T (Lchoice M T α c₁ ε) ^ α ∧
      c₁ * hz M T (Lchoice M T α c₁ ε) ^ α ≤ ε / Real.sqrt 2 := by
  have hm : 1 < (M : ℝ) := by exact_mod_cast (show 1 < M by omega)
  have hm0 : 0 < (M : ℝ) := by linarith
  have hlm : 0 < Real.log (M : ℝ) := Real.log_pos hm
  have hs : 0 < Real.sqrt 2 := by positivity
  have ht : 0 < T ^ α := Real.rpow_pos_of_pos hT _
  have hz0 : 0 < hz M T (Lchoice M T α c₁ ε) := by
    unfold hz; positivity
  have hb : 0 < c₁ * hz M T (Lchoice M T α c₁ ε) ^ α := by positivity
  have hu : 0 < ε / Real.sqrt 2 := div_pos hε hs
  have hlo : 0 < (M : ℝ) ^ (-α) * ε / Real.sqrt 2 := by positivity
  have hl : Real.log (c₁ * hz M T (Lchoice M T α c₁ ε) ^ α) =
      Real.log c₁ + α * (Real.log T - (Lchoice M T α c₁ ε : ℝ) * Real.log M) := by
    rw [Real.log_mul hc₁.ne' (Real.rpow_pos_of_pos hz0 α).ne', Real.log_rpow hz0]
    unfold hz
    rw [Real.log_mul hT.ne' (by positivity), Real.log_zpow]
    push_cast; ring
  have huLog : Real.log (ε / Real.sqrt 2) = Real.log ε - Real.log (Real.sqrt 2) :=
    Real.log_div hε.ne' hs.ne'
  have hloLog : Real.log ((M : ℝ) ^ (-α) * ε / Real.sqrt 2) =
      -α * Real.log M + Real.log ε - Real.log (Real.sqrt 2) := by
    rw [Real.log_div (by positivity) hs.ne', Real.log_mul (by positivity) hε.ne',
      Real.log_rpow hm0]
  let b := Real.log (Real.sqrt 2 * c₁ * T ^ α * ε⁻¹)
  have hblog : b = Real.log (Real.sqrt 2) + Real.log c₁ + α * Real.log T - Real.log ε := by
    dsimp [b]
    rw [Real.log_mul (by positivity) (inv_ne_zero hε.ne'), Real.log_inv,
      Real.log_mul (by positivity) ht.ne', Real.log_mul hs.ne' hc₁.ne', Real.log_rpow hT]
    ring
  have hden : 0 < α * Real.log (M : ℝ) := mul_pos hα hlm
  have hc : b / (α * Real.log (M : ℝ)) ≤ (Lchoice M T α c₁ ε : ℝ) := Int.le_ceil _
  have hcl : (Lchoice M T α c₁ ε : ℝ) < b / (α * Real.log (M : ℝ)) + 1 := Int.ceil_lt_add_one _
  have hcle := (div_le_iff₀ hden).1 hc
  have hclt := (lt_div_iff₀ hden).1 (show (Lchoice M T α c₁ ε : ℝ) - 1 < b / (α * Real.log (M : ℝ)) by linarith)
  constructor
  · apply (Real.log_lt_log_iff hlo hb).1
    rw [hl, hloLog]; nlinarith [hblog]
  · apply (Real.log_le_log_iff hb hu).1
    rw [hl, huLog]; nlinarith [hblog]

#print axioms solution
