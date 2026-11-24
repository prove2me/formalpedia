-- Prove2me | solution 1 for GlobalTheory.HermGlobal.involutive_and_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:16:24.520826+00:00
-- url     : https://prove2.me/submissions/4c4e817a-5527-459c-8e4b-c7c80d5b41f4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_trans
import Theorems.Thm_GlobalTheory_QNorm_IsQuad_finrank_eq_two
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.Inertia.negIndex_neg
attribute [local simp] GlobalTheory.Inertia.posIndex_neg
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open NumberField IsDedekindDomain
open scoped Matrix TensorProduct ComplexConjugate
open GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermGlobal
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.HermGlobal
theorem _root_.solution [Algebra.IsQuadraticExtension F E] {σ : E ≃ₐ[F] E} (hσ : σ ≠ 1) :
    (∀ t, σ (σ t) = t) ∧ (∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) ∧
      ∃ θ : E, θ ≠ 0 ∧ σ θ = -θ := by
  have hcard : Nat.card (E ≃ₐ[F] E) = 2 := by
    refine le_antisymm ?_ ?_
    · rw [← Algebra.IsQuadraticExtension.finrank_eq_two F E]
      simpa using AlgEquiv.card_le (F := F) (K := E)
    · have : Nontrivial (E ≃ₐ[F] E) := ⟨σ, 1, hσ⟩
      exact Finite.one_lt_card
  have : IsGalois F E := IsGalois.of_card_aut_eq_finrank F E
    (hcard.trans (Algebra.IsQuadraticExtension.finrank_eq_two F E).symm)
  obtain ⟨τ, -, hτ⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 hcard
  have hall : ∀ ρ : E ≃ₐ[F] E, ρ = 1 ∨ ρ = σ := fun ρ => by
    by_cases h : ρ = 1
    · exact Or.inl h
    · exact Or.inr ((hτ ρ h).trans (hτ σ hσ).symm)
  have hc : ∀ t, σ (σ t) = t := fun t => by
    rcases hall (σ * σ) with h | h
    · exact DFunLike.congr_fun h t
    · exact absurd (by simpa using h) hσ
  obtain ⟨u, hu⟩ : ∃ u : E, σ u ≠ u := by
    by_contra h
    push Not at h
    exact hσ (AlgEquiv.ext h)
  refine ⟨hc, fun t => ⟨fun h => ?_, ?_⟩, u - σ u, sub_ne_zero.2 hu.symm, ?_⟩
  · refine (IsGalois.mem_range_algebraMap_iff_fixed t).2 fun ρ => ?_
    rcases hall ρ with rfl | rfl
    · rfl
    · exact h
  · rintro ⟨s, rfl⟩
    exact σ.commutes s
  · rw [map_sub, hc, neg_sub]
end GlobalTheory.HermGlobal
