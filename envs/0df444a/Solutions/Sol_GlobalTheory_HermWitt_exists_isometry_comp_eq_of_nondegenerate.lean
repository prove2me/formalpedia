-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_isometry_comp_eq_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:22:08.665929+00:00
-- url     : https://prove2.me/submissions/b9d7c573-db2d-4f6e-a42b-815397129b8c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_of_orthogonal
import Theorems.Thm_GlobalTheory_HermDiag_exists_orthogonal_basis_fin


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermWitt
open Module Matrix GlobalTheory.HermDiag
variable {E : Type*} [Field E] {c : E →+* E} {V : Type*} [AddCommGroup V] [Module E V]
namespace GlobalTheory.HermWitt
theorem _root_.solution (h2 : (2 : E) ≠ 0) {B : V →ₗ[E] V →ₛₗ[c] E}
    (hB : ∀ x y, c (B x y) = B y x) {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {g f : W →ₗ[E] V} (hgf : ∀ a b, B (f a) (f b) = B (g a) (g b))
    (hW : ∀ a, (∀ b, B (g b) (g a) = 0) → a = 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ ∀ a, γ (g a) = f a := by
  obtain ⟨v, hv⟩ := exists_orthogonal_basis_fin h2 (finrank E W)
    (LinearMap.mk₂'ₛₗ (RingHom.id E) c (fun a b => B (g a) (g b))
      (fun _ _ _ => by simp) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp))
    (fun a b => hB _ _) rfl
  replace hv : ∀ i j, i ≠ j → B (g (v i)) (g (v j)) = 0 := hv
  obtain ⟨γ, hγ, e⟩ := exists_isometry_of_orthogonal h2 hB (x := fun i => g (v i))
    (y := fun i => f (v i)) hv (fun i j hij => by rw [hgf]; exact hv i j hij)
    (fun i => (hgf _ _).symm)
    (fun i hi => v.ne_zero i (hW _ fun b => by
      have : (B.flip (g (v i))) ∘ₗ g = 0 := v.ext fun j => by
        by_cases hij : j = i
        · subst hij
          exact hi
        · exact hv j i hij
      exact LinearMap.congr_fun this b))
  refine ⟨γ, hγ, fun a => ?_⟩
  have : γ.toLinearMap ∘ₗ g = f := v.ext e
  exact LinearMap.congr_fun this a
end GlobalTheory.HermWitt
