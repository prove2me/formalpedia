-- Prove2me | solution 1 for GlobalTheory.CM.TenExp.exists_diagonal_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:33:14.872535+00:00
-- url     : https://prove2.me/submissions/7a2e57bf-c35a-4d8f-995e-664eb7f9f328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsDiagonalCoordinates
import Theorems.Thm_GlobalTheory_EigenSplit_coe_eigenBaseChangeEquiv_tmul
import Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_of_field
import Theorems.Thm_GlobalTheory_EigenSplit_isInternal_eigenSub
import Theorems.Thm_GlobalTheory_EigenSplit_isSplitting_of_isUnit_discr
import Theorems.Thm_GlobalTheory_EigenSplit_nonempty_basis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.EigenSplit.coe_eigenBaseChangeEquiv_tmul



set_option autoImplicit false
open NumberField
open scoped TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.CM.TenExp
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CM.TenExp
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (r : 𝓞 E →+* Module.End ℂ V) :
    ∃ (g : ℕ) (B : V ≃ₗ[ℂ] (Fin g → ℂ)) (ty : Fin g → (E →+* ℂ)), ∀ (a : 𝓞 E) v j, B (r a v) j = ty j (a : E) * B v j := by
  classical
  have hs : EigenSplit.IsSplitting fun φ : E →+* ℂ => φ.comp (algebraMap (𝓞 E) E) := by
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  let b := (EigenSplit.isInternal_eigenSub hs r).collectedBasis
    fun φ => Module.finBasis ℂ (EigenSplit.eigenSub r (φ.comp (algebraMap (𝓞 E) E)))
  let e := Fintype.equivFin (Σ φ : E →+* ℂ,
    Fin (Module.finrank ℂ (EigenSplit.eigenSub r (φ.comp (algebraMap (𝓞 E) E)))))
  have hb : ∀ a j, r a (b.reindex e j) = (e.symm j).1 (a : E) • b.reindex e j := fun a j => by
    rw [Module.Basis.reindex_apply]
    exact EigenSplit.mem_eigenSub.1 ((EigenSplit.isInternal_eigenSub hs r).collectedBasis_mem _ (e.symm j)) a
  refine ⟨_, (b.reindex e).equivFun, fun j => (e.symm j).1, fun a v j => ?_⟩
  generalize b.reindex e = b' at hb
  obtain ⟨z, rfl⟩ := b'.equivFun.symm.surjective v
  have : r a (b'.equivFun.symm z) = b'.equivFun.symm fun j => (e.symm j).1 (a : E) * z j := by
    simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, hb, smul_smul, mul_comm]
  rw [this]
  simp only [LinearEquiv.apply_symm_apply]
end GlobalTheory.CM.TenExp
