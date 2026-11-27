-- Prove2me | solution 1 for GlobalTheory.eigenSplitting_of_isUnit_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:37:30.945731+00:00
-- url     : https://prove2.me/submissions/595a00f6-13e6-4eb1-a0cb-ed37c1e53673

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_isProj_proj
import Theorems.Thm_GlobalTheory_EigenSplit_isInternal_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_IsEquivariant_eigenMap_exact
import Theorems.Thm_GlobalTheory_EigenSplit_finite_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_projective_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_free_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv
import Theorems.Thm_GlobalTheory_EigenSplit_eigenSub_baseChangeAction
import Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_prod
import Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_iff_finrank_eq
import Theorems.Thm_GlobalTheory_EigenSplit_charpoly_eq_iff_rankAtStalk_eq
import Theorems.Thm_GlobalTheory_EigenSplit_nonempty_basis
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_conjugateHom
import Theorems.Thm_GlobalTheory_EigenSplit_card_embeddings_of_splits
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isUnit_discr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul

set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open EigenSplit
namespace GlobalTheory
theorem _root_.solution {E : Type*} [Field E] [NumberField E]
    {R : Type*} [CommRing R] :
    (∀ (L : Type) [Field L] [CharZero L] [Algebra (𝓞 L) R] [Fintype (E →+* L)]
      [DecidableEq (E →+* L)], (∀ x : E, ((minpoly ℚ x).map (algebraMap ℚ L)).Splits) →
      Fintype.card (E →+* L) = Module.finrank ℚ E ∧ Nonempty (Module.Basis (E →+* L) ℤ (𝓞 E)) ∧
        ∀ b : Module.Basis (E →+* L) ℤ (𝓞 E),
          (Matrix.of fun φ j => conjugateHom L R φ (b j)).det ^ 2 = (NumberField.discr E : R)) ∧
    ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (σ : ι → 𝓞 E →+* R) (b : Module.Basis ι ℤ (𝓞 E)),
      (Matrix.of fun i j => σ i (b j)).det ^ 2 = (NumberField.discr E : R) →
      IsUnit (NumberField.discr E : R) →
      ∃ h : IsSplitting σ,
        (∃ e : 𝓞 E ⊗[ℤ] R ≃+* (ι → R), ∀ a r i, e (a ⊗ₜ r) i = σ i a * r) ∧
        CompleteOrthogonalIdempotents (idem h) ∧
        (∀ i, splitMap σ (idem h i) = Pi.single i 1) ∧
        ∀ (N : Type) [AddCommGroup N] [Module R N] (ρ : 𝓞 E →+* Module.End R N),
          (∀ i x, x ∈ eigenSub ρ (σ i) ↔ ∀ a, ρ a x = σ i a • x) ∧
          DirectSum.IsInternal (fun i => eigenSub ρ (σ i)) ∧
          (∀ i, LinearMap.IsProj (eigenSub ρ (σ i)) (tensorAction ρ (idem h i))) ∧
          (∀ (R' : Type) [CommRing R'] [Algebra R R'] (i : ι),
            eigenSub (baseChangeAction R' ρ) ((algebraMap R R').comp (σ i))
              = (eigenSub ρ (σ i)).baseChange R' ∧
            Function.Injective ((eigenSub ρ (σ i)).subtype.baseChange R')) ∧
          (∀ (N' N'' : Type) [AddCommGroup N'] [Module R N'] [AddCommGroup N''] [Module R N'']
            (ρ' : 𝓞 E →+* Module.End R N') (ρ'' : 𝓞 E →+* Module.End R N'')
            (f : N →ₗ[R] N') (g : N' →ₗ[R] N'') (hf : IsEquivariant ρ ρ' f)
            (hg : IsEquivariant ρ' ρ'' g), Function.Exact f g →
            ∀ i, Function.Exact (hf.eigenMap (σ i)) (hg.eigenMap (σ i))) ∧
          (Module.Finite R N → ∀ i, Module.Finite R (eigenSub ρ (σ i))) ∧
          (Module.Projective R N → ∀ i, Module.Projective R (eigenSub ρ (σ i))) ∧
          ∀ [Module.Free R N] [Module.Finite R N],
            ((∀ i, Module.Free R (eigenSub ρ (σ i))) → ∀ a, (ρ a).charpoly
              = ∏ i, (X - C (σ i a)) ^ Module.finrank R (eigenSub ρ (σ i))) ∧
            (IsLocalRing R → (∀ i, Module.Free R (eigenSub ρ (σ i))) ∧
              ∀ r : ι → ℕ, (∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) ↔
                ∀ i, Module.finrank R (eigenSub ρ (σ i)) = r i) ∧
            ∀ r : ι → ℕ, (∀ a, (ρ a).charpoly = ∏ i, (X - C (σ i a)) ^ r i) ↔
              ∀ (p : PrimeSpectrum R) i, Module.rankAtStalk (eigenSub ρ (σ i)) p = r i := by
  refine ⟨fun L _ _ _ _ _ hL => ⟨card_embeddings_of_splits hL,
    nonempty_basis (card_embeddings_of_splits hL),
    fun b => det_sq_conjugateHom Function.injective_id b⟩, fun σ b hd hu => ?_⟩
  have h := isSplitting_of_isUnit_discr b hd hu
  refine ⟨h, ⟨splitEquivComm h, splitEquivComm_tmul h⟩, completeOrthogonalIdempotents_idem h,
    splitMap_idem h, fun N _ _ ρ => ⟨fun _ _ => mem_eigenSub, isInternal_eigenSub h ρ,
    isProj_proj h ρ, fun R' _ _ i => ⟨eigenSub_baseChangeAction R' ρ h i, fun s t hst => ?_⟩,
    fun _ _ _ _ _ _ _ _ _ _ hf hg he i => hf.eigenMap_exact h hg i he,
    fun _ => finite_eigenSub h ρ, fun _ => projective_eigenSub h ρ,
    ⟨charpoly_eq_prod h ρ, fun _ => ⟨free_eigenSub h ρ, charpoly_eq_iff_finrank_eq h ρ⟩,
      charpoly_eq_iff_rankAtStalk_eq h ρ⟩⟩⟩
  rw [← coe_eigenBaseChangeEquiv R' ρ h i, ← coe_eigenBaseChangeEquiv R' ρ h i] at hst
  exact (eigenBaseChangeEquiv R' ρ h i).injective (Subtype.ext hst)
end GlobalTheory
