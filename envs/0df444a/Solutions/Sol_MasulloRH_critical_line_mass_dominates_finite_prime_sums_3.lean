-- Prove2me | solution 3 for MasulloRH.critical_line_mass_dominates_finite_prime_sums
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:12:50.14078+00:00
-- url     : https://prove2.me/submissions/bf00ab68-f121-4f0c-a85d-f9f4f26bec5d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_finite_prime_comparison_iff_cofinal_approximation
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_cofinal_approximate_prime_mass_certificates

set_option autoImplicit false

namespace MasulloRH
end MasulloRH
open MasulloRH
theorem solution (N : ℕ) :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2 / 2 + Real.pi / 4 - 37 / 30 +
        (∑ n ∈ Finset.range N, (ArithmeticFunction.vonMangoldt n / (n:ℝ)^(5/2:ℝ) -
          ArithmeticFunction.vonMangoldt n / (n:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4))) :=
  MasulloRH.finite_prime_comparison_iff_cofinal_approximation.mpr
    (MasulloRH.riemannHypothesis_iff_cofinal_approximate_prime_mass_certificates.mp
      mathlib_riemannHypothesis) N
