-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.exact_of_exact_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:55:46.756708+00:00
-- url     : https://prove2.me/submissions/b62babbd-c40b-499c-aeca-acc24bee872d

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
theorem _root_.solution [Decomposition 𝒬] {f : M →ₗ[MvPolynomial ι R] N}
    {g : N →ₗ[MvPolynomial ι R] P} (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap 𝒩 𝒬 g)
    (h : ∀ n, Function.Exact (hf.piece n) (hg.piece n)) : Function.Exact f g := by
  intro y
  constructor
  · intro hy
    obtain ⟨T, hT⟩ := exists_sum_grProj 𝒩 y
    rw [← hT]
    refine (LinearMap.range f).sum_mem fun n _ => ?_
    obtain ⟨m, hm⟩ := (h n ⟨_, proj_mem 𝒩 n y⟩).1 (Subtype.ext (by
      change g (proj 𝒩 n y) = 0
      rw [← hg.proj_apply, hy, map_zero]))
    exact ⟨m, congrArg Subtype.val hm⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨T, hT⟩ := exists_sum_grProj ℳ m
    rw [← hT, map_sum, map_sum]
    exact Finset.sum_eq_zero fun n _ =>
      congrArg Subtype.val ((h n).apply_apply_eq_zero ⟨_, proj_mem ℳ n m⟩)
end GlobalTheory.IsGradedMap
