-- Prove2me | solution 4 for MTT.Cohomology.integration_map
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-07T08:50:10.762465+00:00
-- url     : https://prove2.me/submissions/1ede8c8a-1de0-4dc5-956e-76f2ffe5c421

-- Assemble the common integration map with its published structural properties.
import Theorems.Thm_MTT_Cohomology_integration_linear_map_exists
import Theorems.Thm_MTT_Cohomology_integration_cochain_injective
import Theorems.Thm_MTT_Cohomology_integration_cochain_hecke_equivariant
import Theorems.Thm_MTT_Cohomology_integration_cochain_integral_class

open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k - 2) ℂ,
      Function.Injective I ∧ HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := by
  obtain ⟨I, hI⟩ := integration_linear_map_exists hN hk
  refine ⟨I, ?_, ?_, ?_⟩
  · exact integration_cochain_injective hN hk I hI
  · exact integration_cochain_hecke_equivariant hN hk I hI
  · exact integration_cochain_integral_class hN hk I hI
