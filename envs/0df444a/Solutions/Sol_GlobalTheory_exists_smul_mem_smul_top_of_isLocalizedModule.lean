-- Prove2me | solution 1 for GlobalTheory.exists_smul_mem_smul_top_of_isLocalizedModule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:17.972067+00:00
-- url     : https://prove2.me/submissions/c1b680cf-a58b-437b-9d66-76fd780834cf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]
namespace GlobalTheory
theorem _root_.solution (T : Submonoid R) (g : M →ₗ[R] N)
    [IsLocalizedModule T g] (J : Ideal R) {x : M} (hx : g x ∈ (J • ⊤ : Submodule R N)) :
    ∃ s ∈ T, s • x ∈ (J • ⊤ : Submodule R M) := by
  rw [← Submodule.localized₀_top T g, ← Submodule.localized₀_smul] at hx
  obtain ⟨m, hm, s, hs⟩ := hx
  rw [IsLocalizedModule.mk'_eq_iff, ← LinearMap.map_smul_of_tower,
    IsLocalizedModule.eq_iff_exists T g] at hs
  obtain ⟨t, ht⟩ := hs
  refine ⟨(t * s : T), (t * s).2, ?_⟩
  have : ((t * s : T) : R) • x = (t : R) • m := by
    rw [Submonoid.coe_mul, mul_smul]
    exact ht.symm
  rw [this]
  exact Submodule.smul_mem _ _ hm
end GlobalTheory
