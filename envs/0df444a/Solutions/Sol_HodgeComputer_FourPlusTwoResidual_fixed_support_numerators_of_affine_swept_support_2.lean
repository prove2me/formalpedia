-- Prove2me | solution 2 for HodgeComputer.FourPlusTwoResidual.fixed_support_numerators_of_affine_swept_support
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-25T16:12:28.667849+00:00
-- url     : https://prove2.me/submissions/f1d4619d-2c8e-4d04-93bd-f32b1e23a33f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_fixedSupport_eq_of_n_eq_zero
import Theorems.Thm_HodgeComputer_FourPlusTwoResidual_exists_fixed_support_equation_witness
import Definitions.Def_HodgeComputerFourPlusTwoRationalCurrent

set_option autoImplicit false
noncomputable section

open MvPolynomial
open scoped BigOperators

theorem solution
    (hB : ∃ (B : MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧ ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B)) :
    ∃ (B : MvPolynomial (Fin 3) ℂ) (n : ℕ) (N : Fin 3 → MvPolynomial (Fin 3) ℂ),
      B ≠ 0 ∧
        ¬(HodgeComputer.FourPlusTwoResidual.affineCore ∣ B) ∧
          HodgeComputer.FourPlusTwoResidual.FixedSupportEquation B n N := by
  obtain ⟨B, hB0, hB1⟩ := hB
  obtain ⟨B', n, N, hB'0, hB'1, hFE⟩ :=
    HodgeComputer.FourPlusTwoResidual.exists_fixed_support_equation_witness
  refine ⟨B', n, N, hB'0, hB'1, ?_⟩
  by_cases hn : n = 0
  · -- Exponent-zero branch: the denominator cancels, so the cleared system is the
    -- denominator-free polynomial system 2*(N . grad h) - 3*h*div N = 3*y^3.
    have hzero : 2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore) -
        3 * HodgeComputer.FourPlusTwoResidual.affineCore * (∑ i, pderiv i (N i))
        = 3 * X 1 ^ 3 :=
      HodgeComputer.FourPlusTwoResidual.fixedSupport_eq_of_n_eq_zero
        B' N hB'0 (by simpa [hn] using hFE)
    simp only [HodgeComputer.FourPlusTwoResidual.FixedSupportEquation, hn, Nat.cast_zero,
      zero_mul, sub_zero, Nat.zero_add, pow_one]
    calc 2 * B' * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore)
          - 3 * HodgeComputer.FourPlusTwoResidual.affineCore * (B' * (∑ i, pderiv i (N i)))
        = B' * (2 * (∑ i, N i * pderiv i HodgeComputer.FourPlusTwoResidual.affineCore)
            - 3 * HodgeComputer.FourPlusTwoResidual.affineCore * (∑ i, pderiv i (N i))) := by ring
      _ = B' * (3 * X 1 ^ 3) := by rw [hzero]
      _ = 3 * X 1 ^ 3 * B' := by ring
  · exact hFE
