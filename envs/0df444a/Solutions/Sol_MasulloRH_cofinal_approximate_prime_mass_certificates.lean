-- Prove2me | solution 1 for MasulloRH.cofinal_approximate_prime_mass_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:35:07.424885+00:00
-- url     : https://prove2.me/submissions/3235bdaf-481e-4f9f-8046-e619f2e5537e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_MasulloRH_riemannHypothesis_iff_square_sampled_prime_energy
import Theorems.Thm_MasulloRH_finite_square_prime_energy_cap
import Theorems.Thm_MasulloRH_critical_line_mass_has_explicit_verification_height
import Theorems.Thm_riemannHypothesis_iff_zeros_in_strip_on_line
import Mathlib
open ArithmeticFunction MasulloRH Finset
theorem solution  :
    let P := fun N : ℕ => Real.log 2/2 + Real.pi/4 - 37/30 +
      ∑ j ∈ Finset.range N, (vonMangoldt j/(j:ℝ)^(5/2:ℝ)-vonMangoldt j/(j:ℝ)^(3:ℝ))
    let M := fun F : Finset (ZetaZerosInTraceStrip (1/2)) =>
      ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
        ((z.val.im^2-5)/(2*(z.val.im^2+25/4)*(z.val.im^2+4)))
    ∀ k : ℕ, ∃ N ≥ k, ∃ F : Finset (ZetaZerosInTraceStrip (1/2)), (∀ z ∈ F, z.val.re = 1/2) ∧ P N ≤ M F + 1/((k:ℝ)+1) := by
  have hRH : RiemannHypothesis :=
    riemannHypothesis_iff_square_sampled_prime_energy.2.1.mpr finite_square_prime_energy_cap
  have hline (z : ZetaZerosInTraceStrip (1/2)) : z.val.re=1/2 :=
    (riemannHypothesis_iff_zeros_in_strip_on_line.mp hRH) z.val z.prop.1 z.prop.2.1 z.prop.2.2.1
  dsimp only
  intro k
  obtain ⟨F,_,hF,hp⟩ := critical_line_mass_has_explicit_verification_height k (fun z _ => hline z)
  refine ⟨k,le_rfl,F,hF,hp.trans ?_⟩
  exact le_add_of_nonneg_right (by positivity)
