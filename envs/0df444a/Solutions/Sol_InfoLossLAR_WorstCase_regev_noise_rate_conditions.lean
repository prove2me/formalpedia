-- Prove2me | solution 1 for InfoLossLAR.WorstCase.regev_noise_rate_conditions
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T01:28:33.953347+00:00
-- url     : https://prove2.me/submissions/c8fca84c-f00b-4d1f-848a-7c3e192eedc4

import Definitions.Def_InfoLossLAR_WorstCase_Family

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- The fixed modulus is at least the explicit threshold used to choose it. -/
private theorem famq_lower_bound (lam : ℕ) : 2 ^ 16 * famL lam ^ 64 ≤ famq lam :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64))).1

/-- The fixed modulus is prime, independently of any asymptotic threshold. -/
private theorem famq_prime (lam : ℕ) : (famq lam).Prime :=
  (Nat.find_spec (Nat.exists_infinite_primes (2 ^ 16 * famL lam ^ 64))).2

/-- The source's Gaussian width satisfies Regev's strict dimension condition for λ ≥ 3. -/
private theorem regev_width_condition (lam : ℕ) (hlam : 3 ≤ lam) :
    2 * Real.sqrt (lam : ℝ) < (famσ lam : ℝ) / Real.sqrt 2 := by
  have hlamR : (3 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hroot_sq : Real.sqrt (lam : ℝ) ^ 2 = lam := Real.sq_sqrt (by positivity)
  have hroot_nonneg : 0 ≤ Real.sqrt (lam : ℝ) := Real.sqrt_nonneg _
  have hwidth : (famσ lam : ℝ) = (lam : ℝ) + 2 := by simp [famσ, famL]
  rw [lt_div_iff₀ hsqrt, hwidth]
  have hpoly : (8 : ℝ) * lam < ((lam : ℝ) + 2) ^ 2 := by nlinarith [sq_nonneg ((lam : ℝ) - 3)]
  nlinarith [sq_nonneg (2 * Real.sqrt (lam : ℝ) * Real.sqrt 2 + ((lam : ℝ) + 2))]


/-- The Gaussian width is strictly below the family's modulus at every parameter. -/
private theorem famσ_lt_famq (lam : ℕ) : famσ lam < famq lam := by
  have hspec := famq_lower_bound lam
  have hL : 1 ≤ famL lam := by unfold famL; omega
  have hpow : famL lam ≤ famL lam ^ 64 := le_self_pow₀ hL (by norm_num)
  have hpos : 0 < famL lam ^ 64 := by positivity
  unfold famσ
  omega

end InfoLossLAR.WorstCase

open InfoLossLAR.WorstCase

theorem solution (lam : ℕ) (hlam : 3 ≤ lam) :
    let α : ℝ := (famσ lam : ℝ) / (Real.sqrt 2 * (famq lam : ℝ))
    0 < α ∧ α < 1 ∧ 2 * Real.sqrt (famN lam : ℝ) < α * (famq lam : ℝ) := by
  dsimp only
  have hσ : (0 : ℝ) < (famσ lam : ℝ) := by unfold famσ famL; positivity
  have hq : (0 : ℝ) < (famq lam : ℝ) := by exact_mod_cast (famq_prime lam).pos
  have hsqrt : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrt1 : (1 : ℝ) < Real.sqrt 2 := by
    have := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith
  have hσq : (famσ lam : ℝ) < (famq lam : ℝ) := by exact_mod_cast famσ_lt_famq lam
  refine ⟨by positivity, (div_lt_one (by positivity)).2 ?_, ?_⟩
  · exact hσq.trans (by nlinarith)
  · have heq : (famσ lam : ℝ) / (Real.sqrt 2 * (famq lam : ℝ)) * (famq lam : ℝ) =
        (famσ lam : ℝ) / Real.sqrt 2 := by field_simp
    rw [heq]
    exact regev_width_condition lam hlam
