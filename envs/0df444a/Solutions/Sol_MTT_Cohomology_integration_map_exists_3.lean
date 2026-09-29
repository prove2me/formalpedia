-- Prove2me | solution 3 for MTT.Cohomology.integration_map_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T04:36:14.577063+00:00
-- url     : https://prove2.me/submissions/7cefeab9-3c9d-4b02-9f25-96e511702b1c

import Theorems.Thm_MTT_Cohomology_integration_linear_map_exists
import Theorems.Thm_MTT_Cohomology_integration_cochain_hecke_equivariant
import Theorems.Thm_MTT_Cohomology_integration_cochain_integral_class

open MTT.Cohomology

theorem solution {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ,
      HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := by
  obtain ⟨I, hI⟩ := integration_linear_map_exists hN hk
  exact ⟨I,
    integration_cochain_hecke_equivariant hN hk I hI,
    integration_cochain_integral_class hN hk I hI⟩
