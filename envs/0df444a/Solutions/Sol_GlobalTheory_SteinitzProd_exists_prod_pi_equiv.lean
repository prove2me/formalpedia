-- Prove2me | solution 1 for GlobalTheory.SteinitzProd.exists_prod_pi_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:24:20.833354+00:00
-- url     : https://prove2.me/submissions/6e28c9d1-7c3c-4b34-be47-86e6966ee5be

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FinitelyManyIsoClassesProjectiveNumberField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SteinitzPiIdealsLinearEquivOfClassGroupProd
import Theorems.Thm_GlobalTheory_SteinitzProd_exists_prod_equiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.SteinitzProd
variable {R : Type} [CommRing R] [IsDedekindDomain R]
namespace GlobalTheory.SteinitzProd
theorem _root_.solution (n : ℕ) : ∀ (I : Fin n → (Ideal R)⁰) (K : (Ideal R)⁰),
    ∃ L : (Ideal R)⁰, ClassGroup.mk0 L = ClassGroup.mk0 K * ∏ i, ClassGroup.mk0 (I i) ∧
      Nonempty ((↥(K : Ideal R) × ((i : Fin n) → ↥(I i : Ideal R))) ≃ₗ[R]
        (↥(L : Ideal R) × (Fin n → R))) := by
  induction n with
  | zero =>
    intro I K
    exact ⟨K, by simp, ⟨(LinearEquiv.refl R _).prodCongr (LinearEquiv.ofSubsingleton _ _)⟩⟩
  | succ n ih =>
    intro I K
    obtain ⟨L₁, hL₁, ⟨e₁⟩⟩ := exists_prod_equiv K (I 0)
    obtain ⟨L, hL, ⟨e₂⟩⟩ := ih (fun i => I i.succ) L₁
    refine ⟨L, by rw [hL, hL₁, Fin.prod_univ_succ, mul_assoc], ⟨?_⟩⟩
    exact (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun i => ↥(I i : Ideal R))).symm ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ e₁.prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ (LinearEquiv.refl R R).prodCongr e₂ ≪≫ₗ
      (LinearEquiv.prodAssoc R _ _ _).symm ≪≫ₗ
      (LinearEquiv.prodComm R _ _).prodCongr (LinearEquiv.refl R _) ≪≫ₗ
      LinearEquiv.prodAssoc R _ _ _ ≪≫ₗ
      (LinearEquiv.refl R _).prodCongr (Fin.consLinearEquiv R (fun _ => R))
end GlobalTheory.SteinitzProd
