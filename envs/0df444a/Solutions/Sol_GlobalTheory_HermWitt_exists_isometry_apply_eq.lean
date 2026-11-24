-- Prove2me | solution 1 for GlobalTheory.HermWitt.exists_isometry_apply_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:14.65718+00:00
-- url     : https://prove2.me/submissions/0c140a29-b6e9-44c2-8448-589e332e3b9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Theorems.Thm_GlobalTheory_HermWitt_exists_isometry_of_apply_sub_ne_zero

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
    (hB : ∀ x y, c (B x y) = B y x) {x y : V} (hxy : B x x = B y y) (hx : B x x ≠ 0) :
    ∃ γ : V ≃ₗ[E] V, (∀ z w, B (γ z) (γ w) = B z w) ∧ γ x = y ∧
      ∀ u, B u x = 0 → B u y = 0 → γ u = u := by
  by_cases ha : B x (x - y) = 0
  · have h1 : B x (x - -y) ≠ 0 := by
      have : B x (x - -y) = 2 * B x x := by
        simp only [map_sub, map_neg] at ha ⊢
        linear_combination -ha
      rw [this]
      exact mul_ne_zero h2 hx
    have h3 : B (-y) (-y - y) ≠ 0 := by
      have : B (-y) (-y - y) = 2 * B x x := by
        simp only [map_sub, map_neg, LinearMap.neg_apply, hxy]
        ring
      rw [this]
      exact mul_ne_zero h2 hx
    obtain ⟨γ₁, i₁, e₁, f₁⟩ := exists_isometry_of_apply_sub_ne_zero hB (by simpa using hxy) h1
    obtain ⟨γ₂, i₂, e₂, f₂⟩ := exists_isometry_of_apply_sub_ne_zero hB (by simp) h3
    refine ⟨γ₁.trans γ₂, fun z w => ?_, ?_, fun u hux huy => ?_⟩
    · rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, i₂, i₁]
    · rw [LinearEquiv.trans_apply, e₁, e₂]
    · rw [LinearEquiv.trans_apply, f₁ u (by simp [hux, huy]), f₂ u (by simp [huy])]
  · obtain ⟨γ, i, e, f⟩ := exists_isometry_of_apply_sub_ne_zero hB hxy ha
    exact ⟨γ, i, e, fun u hux huy => f u (by simp [hux, huy])⟩
end GlobalTheory.HermWitt
