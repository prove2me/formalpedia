-- Prove2me | solution 1 for N25.genusFour_numerator_reconstruction
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:03.629036+00:00
-- url     : https://prove2.me/submissions/7772adfb-aba6-4ad7-9436-5e3842504d0f

import Definitions.Def_N25_GenusFourNumerator
import Theorems.Thm_N25_genusFour_reciprocal_coefficient
import Theorems.Thm_N25_newtonFour_coefficients_unique

/-! # Reconstruction from four counts and the genus-four functional equation

The hypotheses retain the degree bound, constant coefficient, Newton identities,
and functional equation explicitly. Geometric producers of these hypotheses are
separate from this integer-polynomial calculation.
-/

namespace N25

/-- Degree eight, Newton identities, and reciprocity determine the numerator. -/
theorem _root_.solution
    (L : Polynomial ℤ) (q a₁ a₂ a₃ a₄ N₁ N₂ N₃ N₄ : ℤ)
    (hq : q ≠ 0) (hdegree : L.natDegree ≤ 8) (hzero : L.coeff 0 = 1)
    (hnewton : CountNewtonFourEquations q N₁ N₂ N₃ N₄
      (L.coeff 1) (L.coeff 2) (L.coeff 3) (L.coeff 4))
    (hcandidate : CountNewtonFourEquations q N₁ N₂ N₃ N₄ a₁ a₂ a₃ a₄)
    (hrec : ∀ i ≤ 8, L.coeff (8 - i) * q ^ i = q ^ 4 * L.coeff i) :
    L = genusFourNumerator q a₁ a₂ a₃ a₄ := by
  obtain ⟨h₁, h₂, h₃, h₄⟩ := newtonFour_coefficients_unique hnewton hcandidate
  have h₈ := genusFour_reciprocal_coefficient hq hrec 0 (by omega)
  have h₇ := genusFour_reciprocal_coefficient hq hrec 1 (by omega)
  have h₆ := genusFour_reciprocal_coefficient hq hrec 2 (by omega)
  have h₅ := genusFour_reciprocal_coefficient hq hrec 3 (by omega)
  norm_num only [Nat.reduceSub, pow_zero, mul_one] at h₈ h₇ h₆ h₅
  rw [hzero] at h₈
  rw [h₁] at h₇
  rw [h₂] at h₆
  rw [h₃] at h₅
  ext n
  by_cases hn : n ≤ 8
  · interval_cases n <;>
      simp only [genusFourNumerator, Polynomial.coeff_add,
        Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one] <;>
      norm_num [hzero, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈]
  · have hlarge : 8 < n := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree hlarge)]
    simp only [genusFourNumerator, Polynomial.coeff_add,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_one]
    split_ifs <;> omega

namespace Endgame

end Endgame

end N25
