-- Prove2me | solution 1 for GlobalTheory.exists_homLoc_bijective_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:01:22.612866+00:00
-- url     : https://prove2.me/submissions/c2445e13-5168-4b9a-8611-f024455577a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomLocBijectiveGrSum
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_IsGradedMap_comp
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
import Theorems.Thm_GlobalTheory_pow_smul_awayFrac
import Theorems.Thm_GlobalTheory_toHomLoc_bijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type} {R : Type} [CommRing R]
namespace GlobalTheory
theorem _root_.solution
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩] [Decomposition 𝒩]
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (hb : Function.Bijective fun m : N => xProd R s • m)
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n, ∀ a ∈ 𝒩 n, ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] 𝒩 n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • (φ z : N) = f m := by
  let e := LinearEquiv.ofBijective _ (toHomLoc_bijective 𝒩 hb n)
  refine ⟨e.symm.toLinearMap ∘ₗ homLocMap hf s n, e.symm.bijective.comp ⟨?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, k, m, hm, rfl⟩ hz
    have hz' : awayMap _ f (awayFrac M (xProd R s) k m) = 0 := congrArg Subtype.val hz
    rw [awayMap_awayFrac, map_eq_zero_iff _ (awayFrac_injective hb.1 k)] at hz'
    exact Subtype.ext (awayFrac_eq_zero_iff.2 (h₁ _ m hm hz'))
  · refine homLocMap_surjective_of hf (fun y => ?_) n
    induction y using Decomposition.inductionOn 𝒩 with
    | zero => exact ⟨0, by simp⟩
    | @homogeneous d a =>
      obtain ⟨k, y, hy⟩ := h₂ d a a.2
      exact ⟨k, y, hy⟩
    | add a b ha hb =>
      obtain ⟨k, ha⟩ := ha
      obtain ⟨j, hb⟩ := hb
      refine ⟨k + j, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [add_comm, pow_add, mul_smul]
        exact Submodule.smul_mem _ _ ha
      · rw [pow_add, mul_smul]
        exact Submodule.smul_mem _ _ hb
  · intro z k m hm
    have h : awayFrac N (xProd R s) 0 (e.symm (homLocMap hf s n z) : N) = awayMap _ f z :=
      congrArg Subtype.val (e.apply_symm_apply (homLocMap hf s n z))
    apply awayFrac_injective hb.1 0
    rw [map_smul]
    erw [h]
    rw [← hm, awayMap_awayFrac, pow_smul_awayFrac]
end GlobalTheory
