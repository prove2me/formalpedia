-- Prove2me | solution 1 for GlobalTheory.HermGlobal.exists_embedding_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:35:08.51916+00:00
-- url     : https://prove2.me/submissions/66314bae-1bea-4279-afd9-f93c979af4a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_HermGlobal_exists_coord
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_SelfDualGenus_exists_coord
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
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E}
namespace GlobalTheory.HermGlobal
theorem _root_.solution (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (h0 : θ ≠ 0) (hθ : σ θ = -θ)
    {d : F} (hd : algebraMap F E d = θ * θ) (ρ : F →+* ℝ) (hρ : ρ d < 0) :
    ∃ τ : E →+* ℂ, (∀ x, τ (σ x) = conj (τ x)) ∧ ∀ s : F, τ (algebraMap F E s) = (ρ s : ℂ) := by
  let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
  have hτ : ∀ s : F, τ (algebraMap F E s) = (ρ s : ℂ) := fun s =>
    ComplexEmbedding.lift_algebraMap_apply E _ s
  have h1 : τ θ * τ θ = (ρ d : ℂ) := by rw [← map_mul, ← hd, hτ]
  have h2 := congrArg Complex.re h1
  have h3 := congrArg Complex.im h1
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h2 h3
  have h4 : (τ θ).re = 0 := by
    by_contra hne
    have : (τ θ).im = 0 := by
      have : (τ θ).re * (τ θ).im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [this] at h2
    nlinarith [mul_self_nonneg (τ θ).re]
  have h5 : conj (τ θ) = -τ θ := by
    apply Complex.ext <;> simp [h4]
  refine ⟨τ, fun x => ?_, hτ⟩
  obtain ⟨a, b, rfl⟩ := exists_coord hc hF h0 hθ x
  simp only [map_add, map_mul, AlgEquiv.commutes, hθ, map_neg, hτ, Complex.conj_ofReal, h5]
end GlobalTheory.HermGlobal
