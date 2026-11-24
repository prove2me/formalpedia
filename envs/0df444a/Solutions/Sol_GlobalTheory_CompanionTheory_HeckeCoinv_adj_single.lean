-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeCoinv.adj_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:55:28.304178+00:00
-- url     : https://prove2.me/submissions/d095f9ee-7002-4b2a-a4b7-d0c49af00588

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_support_finite
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_finsum_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_starH_single
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_inner_phi
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil



set_option autoImplicit false
open CompanionTheory.Rg.Fl
open scoped InnerProductSpace ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCoinv
variable {G : Type} [Group G] {K : Subgroup G}
namespace GlobalTheory.CompanionTheory.HeckeCoinv
theorem _root_.solution {N : ℕ} (Γ : Subgroup G) [∀ x : G ⧸ K, Finite (MulAction.stabilizer Γ x)]
    (hp : IsHeckePair K) (h : Hk K) (φ : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin N))
    (hφ : ∀ x y, ⟪φ (Finsupp.single x 1), φ (Finsupp.single y 1)⟫_ℂ = (cnt Γ x y : ℂ)) (x y : G ⧸ K) :
    ⟪φ (Finsupp.single x 1), φ (h.1 (Finsupp.single y 1))⟫_ℂ =
      ⟪φ ((starH hp h).1 (Finsupp.single x 1)), φ (Finsupp.single y 1)⟫_ℂ := by
  set F := h.1 (Finsupp.single y 1) with hF
  rw [starH_single, ← inner_conj_symm (φ (rowF hp h x)), inner_phi Γ φ hφ y, inner_phi Γ φ hφ x,
    ← finsum_eq, ← finsum_eq]
  have h1 : ∀ γ : Γ, rowF hp h x (γ • y) = conj (F (γ⁻¹ • x)) := by
    intro γ
    rw [rowF_apply]
    congr 1
    have := ent_smul h (γ : G) ((γ⁻¹ : Γ) • x) y
    have h2 : (γ : G) • ((γ⁻¹ : Γ) • x) = x := smul_inv_smul γ x
    rw [h2] at this
    exact this
  have h3 : ∑ᶠ γ : Γ, rowF hp h x (γ • y) = ∑ᶠ γ : Γ, conj (F (γ • x)) := by
    simp only [h1]
    exact finsum_comp_equiv (Equiv.inv Γ) (f := fun γ : Γ => conj (F (γ • x)))
  rw [h3]
  have h4 := AddMonoidHom.map_finsum (starRingEnd ℂ : ℂ →+* ℂ).toAddMonoidHom
    (support_finite (Γ := Γ) F x)
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h4
  rw [← h4]
  simp
end GlobalTheory.CompanionTheory.HeckeCoinv
