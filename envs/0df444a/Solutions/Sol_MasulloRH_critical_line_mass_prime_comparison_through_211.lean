-- Prove2me | solution 1 for MasulloRH.critical_line_mass_prime_comparison_through_211
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:04:45.231845+00:00
-- url     : https://prove2.me/submissions/85694881-8d60-4ebe-9130-f5a28061a2e5

-- Specializes the verified-height and prime-tail comparison of marozols to cutoff 211.
import Theorems.Thm_MasulloRH_critical_line_mass_of_verified_height_and_prime_tail
import Theorems.Thm_MasulloRH_certified_height_99998_reference_budget
import Theorems.Thm_MasulloRH_certified_prime_tail_from_211
open ArithmeticFunction MasulloRH

theorem solution (N : ℕ) (hN : N ≤ 211) :
    ∃ F : Finset (ZetaZerosInTraceStrip (1/2)),
      (∀ z ∈ F, z.val.re = 1/2) ∧
      Real.log 2 / 2 + Real.pi / 4 - 37 / 30 +
        (∑ j ∈ Finset.range N, (vonMangoldt j / (j:ℝ)^(5/2:ℝ) -
          vonMangoldt j / (j:ℝ)^(3:ℝ))) ≤
        ∑ z ∈ F, (analyticOrderNatAt riemannZeta z.val:ℝ) *
          ((z.val.im^2 - 5) / (2 * (z.val.im^2 + 25/4) * (z.val.im^2+4))) := by
  obtain ⟨P, hp, hmass⟩ := certified_prime_tail_from_211
  obtain ⟨hheight, herr⟩ := certified_height_99998_reference_budget
  exact critical_line_mass_of_verified_height_and_prime_tail 49998 N P
    (fun p h ↦ hN.trans (hp p h).2.1) hheight (herr.trans hmass)
