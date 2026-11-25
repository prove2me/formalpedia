-- Prove2me | solution 1 for GlobalTheory.exists_homLoc_bijective_grSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:38:04.40216+00:00
-- url     : https://prove2.me/submissions/4fe4a25e-479e-45b8-80da-37b377763d16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsHomLocBijectiveGrSum
import Theorems.Thm_GlobalTheory_GrSum_X_smul_bijective
import Theorems.Thm_GlobalTheory_xProd_smul_bijective_of
import Theorems.Thm_GlobalTheory_exists_homLoc_bijective_of
import Theorems.Thm_GlobalTheory_IsGradedMap_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f) (s : Finset ι)
    (hb : ∀ i ∈ s, ∀ t, Function.Bijective (x i t))
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n (a : A n), ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • GrSum.of hx n a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] A n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • GrSum.of hx n (φ z) = f m := by
  obtain ⟨ψ, hψ, hψ'⟩ := exists_homLoc_bijective_of hf s
    (xProd_smul_bijective_of s fun i hi => GrSum.X_smul_bijective hx (hb i hi)) h₁
    (by rintro n _ ⟨a, rfl⟩; exact h₂ n a) n
  refine ⟨(GrSum.pieceEquiv hx n).symm.toLinearMap ∘ₗ ψ,
    (GrSum.pieceEquiv hx n).symm.bijective.comp hψ, fun z k m e => ?_⟩
  rw [← hψ' z k m e]
  exact congrArg (fun w : GrSum.grading hx n => xProd R s ^ k • (w : GrSum hx))
    ((GrSum.pieceEquiv hx n).apply_symm_apply (ψ z))
end GlobalTheory
