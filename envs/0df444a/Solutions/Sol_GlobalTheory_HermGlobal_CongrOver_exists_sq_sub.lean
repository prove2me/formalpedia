-- Prove2me | solution 1 for GlobalTheory.HermGlobal.CongrOver.exists_sq_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:44:59.28529+00:00
-- url     : https://prove2.me/submissions/4e03efea-c8b0-4868-b1ad-592cf3cbf882

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_HermGlobal_CongrOver_det_norm
import Theorems.Thm_GlobalTheory_HermGlobal_exists_coord
import Theorems.Thm_GlobalTheory_HermLocal_CongrOver_det_norm
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
import Theorems.Thm_GlobalTheory_Published_Landherr_det_norm
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
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {σ : E ≃ₐ[F] E}
namespace GlobalTheory.HermGlobal
namespace CongrOver
theorem _root_.solution [CharZero E] (hc : ∀ t, σ (σ t) = t)
    (hF : ∀ t : E, σ t = t ↔ ∃ s : F, algebraMap F E s = t) {θ : E} (h0 : θ ≠ 0) (hθ : σ θ = -θ)
    {d : F} (hd : algebraMap F E d = θ * θ) {A : Type*} [Field A] [Algebra F A] {r : ℕ}
    {G G' : Matrix (Fin r) (Fin r) E} (hd' : G'.det ≠ 0) (h : CongrOver σ A G G') {a : F}
    (ha : algebraMap F E a = G.det / G'.det) :
    ∃ p q : A, algebraMap F A a = p ^ 2 - algebraMap F A d * q ^ 2 := by
  obtain ⟨z, hz⟩ := h.det_norm hd'
  have hs : ∀ s : F, (1 : A) ⊗ₜ[F] algebraMap F E s = algebraMap A (A ⊗[F] E) (algebraMap F A s) := by
    intro s
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.algebraMap_apply' s).symm
  obtain ⟨p, q, rfl⟩ : ∃ p q : A, z = algebraMap A _ p + algebraMap A _ q * (1 : A) ⊗ₜ[F] θ := by
    clear hz
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul u x =>
      obtain ⟨s, t, rfl⟩ := exists_coord hc hF h0 hθ x
      refine ⟨u * algebraMap F A s, u * algebraMap F A t, ?_⟩
      rw [map_mul, map_mul, ← hs, ← hs]
      simp [TensorProduct.tmul_add]
    | add x y hx hy =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨p', q', rfl⟩ := hy
      exact ⟨p + p', q + q', by simp only [map_add]; ring⟩
  refine ⟨p, q, (algebraMap A (A ⊗[F] E)).injective ?_⟩
  have h1 : baseConj σ A ((1 : A) ⊗ₜ[F] θ) = -((1 : A) ⊗ₜ[F] θ) := by
    rw [Algebra.TensorProduct.map_tmul, ← TensorProduct.tmul_neg, ← hθ]
    rfl
  have h2 : algebraMap A (A ⊗[F] E) (algebraMap F A d) = (1 : A) ⊗ₜ[F] θ * (1 : A) ⊗ₜ[F] θ := by
    rw [← hs, hd, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [← hs, ha, hz, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, h1, map_sub, map_mul,
    map_pow, map_pow, h2]
  ring
end CongrOver
end GlobalTheory.HermGlobal
