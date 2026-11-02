-- Prove2me | solution 1 for NoSignalPA.sum_mu
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:44:41.312588+00:00
-- url     : https://prove2.me/submissions/5ce9a807-7963-400f-ae51-1cae73b98544

import Mathlib
import Definitions.Def_NoSignalPA_gammaVec
import Definitions.Def_NoSignalPA_ones

namespace NoSignalPASumMuAux

/-- One system: `Σ_t γ_t(a, b, x, y) = 1/4`. -/
lemma gammaCoef_sum (a b x y : Bool) :
    ∑ t : Bool, NoSignalPA.gammaCoef t a b x y = (4 : ℝ)⁻¹ := by
  rw [Fintype.sum_bool]
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp [NoSignalPA.gammaCoef, NoSignalPA.cell] <;> norm_num

/-- One system: `Σ_t γ_t(a, b, x, y)² ≤ 25^{[a ⊕ b ⊕ xy]} / 32`. -/
lemma gammaCoef_sq_sum (a b x y : Bool) :
    ∑ t : Bool, NoSignalPA.gammaCoef t a b x y ^ 2 ≤
      (32 : ℝ)⁻¹ * 25 ^ (if xor (xor a b) (x && y) then 1 else 0) := by
  rw [Fintype.sum_bool]
  cases a <;> cases b <;> cases x <;> cases y <;>
    simp [NoSignalPA.gammaCoef, NoSignalPA.cell] <;> norm_num

end NoSignalPASumMuAux

open NoSignalPASumMuAux in
theorem solution {Nr : ℕ} (a₀ b₀ x₀ y₀ : NoSignalPA.Str Nr) :
    ∑ s : NoSignalPA.Str Nr, NoSignalPA.gammaVec s a₀ b₀ x₀ y₀ = ((4 : ℝ) ^ Nr)⁻¹ ∧
      ∑ s : NoSignalPA.Str Nr, (NoSignalPA.gammaVec s a₀ b₀ x₀ y₀) ^ 2
        ≤ ((2 : ℝ) ^ (5 * Nr))⁻¹
            * 5 ^ (2 * NoSignalPA.ones (fun i => xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i))) := by
  refine ⟨?_, ?_⟩
  · -- the sum factorizes over the systems
    unfold NoSignalPA.gammaVec
    rw [← Fintype.prod_sum (fun i t => NoSignalPA.gammaCoef t (a₀ i) (b₀ i) (x₀ i) (y₀ i))]
    simp only [gammaCoef_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  · unfold NoSignalPA.gammaVec
    simp only [← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun i t => NoSignalPA.gammaCoef t (a₀ i) (b₀ i) (x₀ i) (y₀ i) ^ 2)]
    calc ∏ i, ∑ t : Bool, NoSignalPA.gammaCoef t (a₀ i) (b₀ i) (x₀ i) (y₀ i) ^ 2
        ≤ ∏ i, ((32 : ℝ)⁻¹ * 25 ^ (if xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i) then 1 else 0)) :=
          Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun t _ => sq_nonneg _)
            (fun i _ => gammaCoef_sq_sum _ _ _ _)
      _ = ((2 : ℝ) ^ (5 * Nr))⁻¹
            * 5 ^ (2 * NoSignalPA.ones (fun i => xor (xor (a₀ i) (b₀ i)) (x₀ i && y₀ i))) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, inv_pow, NoSignalPA.ones, Finset.card_filter,
            pow_mul, pow_mul]
          norm_num
