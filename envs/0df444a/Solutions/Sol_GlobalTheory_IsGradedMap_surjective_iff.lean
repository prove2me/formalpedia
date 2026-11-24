-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.surjective_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:23:14.203517+00:00
-- url     : https://prove2.me/submissions/6469febb-4bea-45fc-bc63-22fc992f94cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
open GlobalTheory.IsGradedMap
variable {ℳ : ℤ → Submodule R M} {𝒩 : ℤ → Submodule R N} {𝒬 : ℤ → Submodule R P}
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
  [IsScalarTower R (MvPolynomial ι R) P]
variable [Decomposition ℳ] [Decomposition 𝒩]
namespace GlobalTheory.IsGradedMap
theorem _root_.solution {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) :
    Function.Surjective f ↔ ∀ n, Function.Surjective (hf.piece n) := by
  refine ⟨fun h n y => ?_, fun h y => ?_⟩
  · obtain ⟨m, hm, e⟩ := hf.exists_mem_of_mem_range y.2 (h y)
    exact ⟨⟨m, hm⟩, Subtype.ext e⟩
  · obtain ⟨T, hT⟩ := exists_sum_grProj 𝒩 y
    rw [← hT]
    refine (LinearMap.range f).sum_mem fun n _ => ?_
    obtain ⟨m, hm⟩ := h n ⟨_, proj_mem 𝒩 n y⟩
    exact ⟨m, congrArg Subtype.val hm⟩
end GlobalTheory.IsGradedMap
