-- Prove2me | solution 1 for GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:55:42.487928+00:00
-- url     : https://prove2.me/submissions/9e7a56e6-3b42-49dc-8606-84f967bfcf5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsAnisotropicOrthogonalBasisHermitian
import Theorems.Thm_GlobalTheory_HermDiag_congr_diagonal_of_orthogonal
import Theorems.Thm_GlobalTheory_HermDiag_det_of_basis_ne_zero
import Theorems.Thm_GlobalTheory_HermDiag_dotProduct_mulVec_comp_eq_sum
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_dotProduct
import Theorems.Thm_GlobalTheory_HermDiag_ne_zero_of_congr_diagonal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep
namespace GlobalTheory.UnRep
theorem _root_.solution :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G →
      ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧
        (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  intro F E _ _ _ _ _ c n G ⟨hc, _, hG, hdet⟩
  let σ : E →+* E := (c : E →+* E)
  have he : ∀ x y : Fin n → E, hermE c G x y = x ⬝ᵥ G *ᵥ (σ ∘ y) := fun x y =>
    (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm
  obtain ⟨v, hv⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero hc hG
  have hd := GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv
  refine ⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩
  · rw [he]
    exact GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd hdet i
  · rw [he]
    exact hv i j hij
end GlobalTheory.UnRep
