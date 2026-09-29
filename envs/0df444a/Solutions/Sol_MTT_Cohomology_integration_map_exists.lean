-- Prove2me | solution 1 for MTT.Cohomology.integration_map_exists
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-06T23:36:05.913269+00:00
-- url     : https://prove2.me/submissions/016e38c0-c25c-4b01-9e29-2ccc96ffbc1a

import Theorems.Thm_MTT_Cohomology_integration_linear_map_exists
import Theorems.Thm_MTT_Cohomology_integration_cochain_hecke_equivariant
import Theorems.Thm_MTT_Cohomology_integration_cochain_integral_class

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ,
      HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := by
  obtain ⟨I, hI⟩ := MTT.Cohomology.integration_linear_map_exists hN hk
  exact ⟨I,
    MTT.Cohomology.integration_cochain_hecke_equivariant hN hk I hI,
    MTT.Cohomology.integration_cochain_integral_class hN hk I hI⟩
