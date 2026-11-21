-- Prove2me | solution 1 for NymanBeurling.arbitrarily_small_remainder_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @ibecca
-- created : 2026-11-21T00:52:42.746264+00:00
-- url     : https://prove2.me/submissions/2f831c20-bcbc-4c89-9ae0-f0ff81f5d156
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_NymanBeurling_real_certificate_has_rational_rounding
import Theorems.Thm_NymanBeurling_damped_moebius_mean_square_approximation

set_option autoImplicit false
open scoped BigOperators

theorem solution (J : ℕ) :
    ∃ (c : ℕ →₀ ℚ) (H : ℕ), ((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) < 1/(J+1 : ℚ) := by
  classical
  let η : ℝ := 1 / (J+1 : ℝ)
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨N, ε, hε, hεhalf, happrox⟩ :=
    NymanBeurling.damped_moebius_mean_square_approximation (η/2) (by positivity)
  let b : Fin N → ℝ := fun k => -((ArithmeticFunction.moebius (k.val+2) : ℝ) / (k.val+2 : ℝ)^ε)
  let B : ℝ := (1 + ∑ k : Fin N, |b k|)^2
  obtain ⟨H, hH⟩ := exists_nat_gt (B / (η/2))
  have htail : B / (H+1 : ℝ) < η/2 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < H+1)).2
    have := (div_lt_iff₀ (by positivity : (0 : ℝ) < η/2)).1 hH
    nlinarith
  have hfinite : (∑ n ∈ Finset.range H,
      (1 - ∑ k : Fin N, b k * (((n+1) % (k.val+2) : ℕ) : ℝ) / (k.val+2 : ℝ))^2 /
        ((n+1 : ℝ)*(n+2 : ℝ))) < η/2 := by
    simpa only [b, neg_mul, neg_div, Finset.sum_neg_distrib, sub_neg_eq_add] using happrox H
  obtain ⟨c, hc, hcost⟩ := NymanBeurling.real_certificate_has_rational_rounding N H b η
    (by change _ + B / (H+1 : ℝ) < η; linarith)
  refine ⟨c, H, ?_⟩
  apply (Rat.cast_lt (K := ℝ)).mp
  have hηcast : ((1 / (J+1 : ℚ) : ℚ) : ℝ) = η := by simp [η]
  rw [hηcast]
  exact hcost
