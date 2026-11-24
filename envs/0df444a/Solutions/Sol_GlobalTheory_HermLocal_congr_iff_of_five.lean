-- Prove2me | solution 1 for GlobalTheory.HermLocal.congr_iff_of_five
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:55:17.303838+00:00
-- url     : https://prove2.me/submissions/0c520717-8016-4525-8844-ebe1723eec26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_GlobalTheory_HermLocal_congr_diagonal_of_five
import Theorems.Thm_GlobalTheory_HermDiag_exists_congr_diagonal
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
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
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermLocal
variable {K L : Type*} [Field K] [Field L] [Algebra K L] {c : L →+* L}
namespace GlobalTheory.HermLocal
theorem _root_.solution (h2 : (2 : K) ≠ 0)
    (H : ∀ a : Fin 5 → K, ∃ x : Fin 5 → K, x ≠ 0 ∧ ∑ i, a i * x i ^ 2 = 0)
    [Algebra.IsQuadraticExtension K L] (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1) {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) L} (hG : ∀ a b, σ (G a b) = G b a)
    (hG' : ∀ a b, σ (G' a b) = G' b a) (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix (Fin r) (Fin r) L, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) ↔
      ∃ x : L, G.det / G'.det = x * σ x := by
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (map_ne_zero _).2 h2
  have hcard : Nat.card (L ≃ₐ[K] L) = 2 := by
    refine le_antisymm ?_ ?_
    · rw [← Algebra.IsQuadraticExtension.finrank_eq_two K L]
      simpa using AlgEquiv.card_le (F := K) (K := L)
    · have : Nontrivial (L ≃ₐ[K] L) := ⟨σ, 1, hσ⟩
      exact Finite.one_lt_card
  have : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L
    (hcard.trans (Algebra.IsQuadraticExtension.finrank_eq_two K L).symm)
  obtain ⟨τ, -, hτ⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[K] L)).1 hcard
  have hall : ∀ ρ : L ≃ₐ[K] L, ρ = 1 ∨ ρ = σ := fun ρ => by
    by_cases h : ρ = 1
    · exact Or.inl h
    · exact Or.inr ((hτ ρ h).trans (hτ σ hσ).symm)
  have hc : ∀ t, (σ : L →+* L) ((σ : L →+* L) t) = t := fun t => by
    rcases hall (σ * σ) with h | h
    · exact DFunLike.congr_fun h t
    · exact absurd (by simpa using h) hσ
  have hF : ∀ t : L, (σ : L →+* L) t = t ↔ ∃ s : K, algebraMap K L s = t := fun t => by
    constructor
    · intro h
      refine (IsGalois.mem_range_algebraMap_iff_fixed t).2 fun ρ => ?_
      rcases hall ρ with rfl | rfl
      · rfl
      · exact h
    · rintro ⟨s, rfl⟩
      exact σ.commutes s
  obtain ⟨u, hu⟩ : ∃ u : L, σ u ≠ u := by
    by_contra h
    push Not at h
    exact hσ (AlgEquiv.ext h)
  have hθ : (σ : L →+* L) (u - σ u) = -(u - σ u) := by
    rw [map_sub, show (σ : L →+* L) (σ u) = u from hc u, neg_sub]
    rfl
  constructor
  · intro h
    obtain ⟨x, -, hx⟩ := (show Congr (σ : L →+* L) G G' from h).symm.det
    exact ⟨x, by rw [hx, mul_div_cancel_right₀ _ hd']; rfl⟩
  · rintro ⟨x, hx⟩
    obtain ⟨P, g, hP, hPg, hg, hg0⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2L hc (G := G) hG
    obtain ⟨P', g', hP', hPg', hg', hg0'⟩ := GlobalTheory.HermDiag.exists_congr_diagonal h2L hc (G := G') hG'
    have h1 : Congr (σ : L →+* L) G (Matrix.diagonal g) := ⟨P, hP, hPg.symm⟩
    have h1' : Congr (σ : L →+* L) G' (Matrix.diagonal g') := ⟨P', hP', hPg'.symm⟩
    refine (h1.trans (congr_diagonal_of_five h2 H hc hF (sub_ne_zero.2 hu.symm) hθ r g g' hg hg'
      (hg0 hd) (hg0' hd') ?_)).trans h1'.symm
    obtain ⟨y, -, hy⟩ := h1.det
    obtain ⟨y', -, hy'⟩ := h1'.symm.det
    rw [div_eq_iff hd'] at hx
    rw [Matrix.det_diagonal] at hy hy'
    refine ⟨y * x * y', ?_⟩
    rw [hy, hx, hy']
    simp only [map_mul, RingHom.coe_coe]
    ring
end GlobalTheory.HermLocal
