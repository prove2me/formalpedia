-- Prove2me | solution 1 for MTT.Cohomology.integration_map
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-06T16:47:31.122621+00:00
-- url     : https://prove2.me/submissions/4ffb1f04-e559-495a-9c04-11ed81093163

import Theorems.Thm_MTT_Cohomology_integration_linear_map_exists
import Theorems.Thm_MTT_Cohomology_integration_cochain_injective
import Theorems.Thm_MTT_Cohomology_integration_cochain_hecke_equivariant
import Theorems.Thm_MTT_Cohomology_integration_cochain_integral_class

set_option autoImplicit false
noncomputable section
open scoped BigOperators TensorProduct
open MTT.Cohomology

theorem solution
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k) :
    ∃ I : CuspForm (MTT.GammaOne N) (k : ℤ) →ₗ[ℂ] Hc N (k-2) ℂ,
      Function.Injective I ∧ HeckeEquivariant I ∧ ∀ f, IntegralClass f (I f) := by
  obtain ⟨I, hI⟩ :=
    MTT.Cohomology.integration_linear_map_exists hN hk
  exact ⟨I,
    MTT.Cohomology.integration_cochain_injective hN hk I hI,
    MTT.Cohomology.integration_cochain_hecke_equivariant hN hk I hI,
    MTT.Cohomology.integration_cochain_integral_class hN hk I hI⟩
