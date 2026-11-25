-- Prove2me | solution 1 for GlobalTheory.Inertia.posIndex_submatrix_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:43:16.650215+00:00
-- url     : https://prove2.me/submissions/6d1b3c0f-70cc-41c6-92f9-269eca9bbb30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_PosIndexMapEqCardOfCongrDiagonal
import Theorems.Thm_GlobalTheory_Inertia_isGreatest_posIndex
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.Inertia.negIndex_neg

set_option autoImplicit false
open GlobalTheory GlobalTheory.Inertia
open Module Matrix ReciprocityTheory.ChartRestriction.G
open scoped ComplexConjugate
variable {n m : Type*} [Fintype n] [Fintype m]
namespace GlobalTheory.Inertia
theorem _root_.solution (G : Matrix n n ℂ) (e : m ≃ n) :
    posIndex (G.submatrix e e) = posIndex G := by
  have h : ∀ x : n → ℂ, (x ∘ e) ⬝ᵥ G.submatrix e e *ᵥ star (x ∘ e) = x ⬝ᵥ G *ᵥ star x := by
    intro x
    have h1 : star (x ∘ e) ∘ e.symm = star x := by
      ext k
      simp
    rw [submatrix_mulVec_equiv, h1]
    exact comp_equiv_dotProduct_comp_equiv x (G *ᵥ star x) e
  let L : (n → ℂ) ≃ₗ[ℂ] (m → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ e
  have hL : ∀ x, L x = x ∘ e := fun _ => rfl
  refine (isGreatest_posIndex _).unique ?_
  have hs : posDims (G.submatrix e e) = posDims G := by
    ext d
    constructor
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map L.symm.toLinearMap, LinearEquiv.finrank_map_eq _ _, ?_⟩
      rintro _ ⟨y, hy, rfl⟩ h0
      rw [← h, ← hL]
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact hW y hy (by rintro rfl; simp at h0)
    · rintro ⟨W, rfl, hW⟩
      refine ⟨W.map L.toLinearMap, LinearEquiv.finrank_map_eq _ _, ?_⟩
      rintro _ ⟨y, hy, rfl⟩ h0
      simp only [LinearEquiv.coe_coe, hL, h]
      exact hW y hy (by rintro rfl; simp at h0)
  rw [hs]
  exact isGreatest_posIndex G
end GlobalTheory.Inertia
