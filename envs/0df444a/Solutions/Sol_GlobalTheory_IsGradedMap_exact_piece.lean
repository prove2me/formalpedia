-- Prove2me | solution 1 for GlobalTheory.IsGradedMap.exact_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:22:33.93965+00:00
-- url     : https://prove2.me/submissions/c32af6b9-ed8e-4698-86c2-b9a648a22ce4

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
theorem _root_.solution {f : M →ₗ[MvPolynomial ι R] N} {g : N →ₗ[MvPolynomial ι R] P}
    (hf : IsGradedMap ℳ 𝒩 f) (hg : IsGradedMap 𝒩 𝒬 g) (h : Function.Exact f g) (n : ℤ) :
    Function.Exact (hf.piece n) (hg.piece n) := by
  intro y
  constructor
  · intro hy
    obtain ⟨m, hm, e⟩ := hf.exists_mem_of_mem_range y.2 ((h y).1 (congrArg Subtype.val hy))
    exact ⟨⟨m, hm⟩, Subtype.ext e⟩
  · rintro ⟨m, rfl⟩
    exact Subtype.ext (h.apply_apply_eq_zero m)
end GlobalTheory.IsGradedMap
