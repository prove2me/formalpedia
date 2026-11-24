-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.injective_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:45.403699+00:00
-- url     : https://prove2.me/submissions/aaa35150-ceda-47c1-bc17-7df998242c32

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
    Function.Injective f ↔ ∀ n, Function.Injective (hf.piece n) := by
  refine ⟨fun h n a b hab => Subtype.ext (h (congrArg Subtype.val hab)), fun h => ?_⟩
  rw [injective_iff_map_eq_zero]
  intro m hm
  obtain ⟨T, hT⟩ := exists_sum_grProj ℳ m
  rw [← hT]
  refine Finset.sum_eq_zero fun n _ => congrArg Subtype.val
    ((injective_iff_map_eq_zero _).1 (h n) ⟨_, proj_mem ℳ n m⟩ (Subtype.ext ?_))
  change f (proj ℳ n m) = 0
  rw [← hf.proj_apply, hm, map_zero]
end GlobalTheory.IsGradedMap
