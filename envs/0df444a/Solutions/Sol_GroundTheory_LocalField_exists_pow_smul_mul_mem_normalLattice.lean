-- Prove2me | solution 1 for GroundTheory.LocalField.exists_pow_smul_mul_mem_normalLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:31.243866+00:00
-- url     : https://prove2.me/submissions/e18a5a57-9ce9-4ce2-a764-168a833e44c9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_UnitsBasic
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Theorems.Thm_GroundTheory_LocalField_exists_pow_smul_mem_normalLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Finset
variable {K L : Type*} [Field K] [ValuativeRel K] [Field L] [Algebra K L]
variable [FiniteDimensional K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]
  [ValuativeExtension K L]
variable (π : 𝒪[K]) (θ : L)
variable [IsGalois K L]
omit [ValuativeRel L] [ValuativeExtension K L]
namespace GroundTheory.LocalField
theorem _root_.solution (hπ : Irreducible π)
    (hθ : LinearIndependent K fun σ : Gal(L/K) => σ θ) :
    ∃ r, ∀ σ τ : Gal(L/K), π ^ r • (σ θ * τ θ) ∈ normalLattice π θ 0 := by
  choose n hn using fun p : Gal(L/K) × Gal(L/K) =>
    exists_pow_smul_mem_normalLattice π θ hπ hθ (p.1 θ * p.2 θ)
  exact ⟨univ.sup n, fun σ τ => hn (σ, τ) _ (le_sup (mem_univ (σ, τ)))⟩
end GroundTheory.LocalField
