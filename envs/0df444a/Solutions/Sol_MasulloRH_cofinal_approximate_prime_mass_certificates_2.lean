-- Prove2me | solution 2 for MasulloRH.cofinal_approximate_prime_mass_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:21.875186+00:00
-- url     : https://prove2.me/submissions/e4b3edfe-8650-4041-8fd7-4de68a2c842e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_mathlib_riemannHypothesis
import Theorems.Thm_MasulloRH_riemannHypothesis_iff_cofinal_approximate_prime_mass_certificates

open ArithmeticFunction MasulloRH Finset

theorem solution :
    let P := fun N : ℕ => Real.log 2/2 + Real.pi/4 - 37/30 +
      ∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))
    let M := fun F : Finset (ZetaZerosInTraceStrip (1/2)) =>
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
    ∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), (∀ z ∈ F, z.val.re = 1/2) ∧ P N ≤ M F + 1/((k:ℝ)+1) :=
  Iff.mp MasulloRH.riemannHypothesis_iff_cofinal_approximate_prime_mass_certificates
    mathlib_riemannHypothesis
