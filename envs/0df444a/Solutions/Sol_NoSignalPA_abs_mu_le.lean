-- Prove2me | solution 1 for NoSignalPA.abs_mu_le
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:43:06.762308+00:00
-- url     : https://prove2.me/submissions/14600202-5436-4618-8a35-59fcd3c935e7

import Mathlib
import Definitions.Def_NoSignalPA_gammaVec
import Definitions.Def_NoSignalPA_ones

namespace NoSignalPAAbsMuAux

/-- One system: `|γ_t(a, b, x, y)| ≤ 5^{[a ⊕ b ⊕ xy]} / 8`. -/
lemma gammaCoef_abs_le (t a b x y : Bool) :
    |NoSignalPA.gammaCoef t a b x y| ≤
      5 ^ (if xor (xor a b) (x && y) then 1 else 0) * (8 : ℝ)⁻¹ := by
  cases t <;> cases a <;> cases b <;> cases x <;> cases y <;>
    simp [NoSignalPA.gammaCoef, NoSignalPA.cell] <;> norm_num

end NoSignalPAAbsMuAux

open NoSignalPAAbsMuAux in
theorem solution {Nr : ℕ} (s a₀ b₀ x₀ y₀ : NoSignalPA.Str Nr) :
    |NoSignalPA.gammaVec s a₀ b₀ x₀ y₀|
      ≤ 5 ^ NoSignalPA.ones (fun i => xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i)) *
          ((8 : ℝ) ^ Nr)⁻¹ := by
  unfold NoSignalPA.gammaVec
  rw [Finset.abs_prod]
  calc ∏ i, |NoSignalPA.gammaCoef (s i) (a₀ i) (b₀ i) (x₀ i) (y₀ i)|
      ≤ ∏ i, (5 ^ (if xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i) then 1 else 0) * (8 : ℝ)⁻¹) :=
        Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => gammaCoef_abs_le _ _ _ _ _)
    _ = 5 ^ NoSignalPA.ones (fun i => xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i)) *
          ((8 : ℝ) ^ Nr)⁻¹ := by
        rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, inv_pow, NoSignalPA.ones, Finset.card_filter]
