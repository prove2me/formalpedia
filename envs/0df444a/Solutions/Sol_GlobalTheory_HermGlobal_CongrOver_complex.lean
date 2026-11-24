-- Prove2me | solution 1 for GlobalTheory.HermGlobal.CongrOver.complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:13:28.025438+00:00
-- url     : https://prove2.me/submissions/af9176a5-cbcf-4167-ae0e-6878796eb23e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_Inertia_negIndex_neg
import Theorems.Thm_GlobalTheory_Inertia_posIndex_neg
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm
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
variable {σ : E ≃ₐ[F] E} {A : Type*} [CommRing A] [Algebra F A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
namespace GlobalTheory.HermGlobal
namespace CongrOver
theorem _root_.solution (h : CongrOver σ A G G') (τ : E →+* ℂ) (hτ : ∀ x, τ (σ x) = conj (τ x))
    (ψ : A →+* ℂ) (hψ : ∀ a, conj (ψ a) = ψ a)
    (hψτ : ∀ s : F, ψ (algebraMap F A s) = τ (algebraMap F E s)) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj := by
  obtain ⟨P, hP, h⟩ := h
  letI : Algebra F ℂ := (τ.comp (algebraMap F E)).toAlgebra
  let ψ' : A →ₐ[F] ℂ := { ψ with commutes' := hψτ }
  let τ' : E →ₐ[F] ℂ := { τ with commutes' := fun _ => rfl }
  let Φ : A ⊗[F] E →+* ℂ := (Algebra.TensorProduct.productMap ψ' τ').toRingHom
  have hΦ : ∀ (a : A) (x : E), Φ (a ⊗ₜ[F] x) = ψ a * τ x := fun a x =>
    Algebra.TensorProduct.productMap_apply_tmul ψ' τ' a x
  have hc : ∀ z, Φ (baseConj σ A z) = conj (Φ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      rw [Algebra.TensorProduct.map_tmul, hΦ, hΦ, map_mul, hψ, ← hτ]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
  have e : ∀ M : Matrix (Fin r) (Fin r) E, (M.map fun x => (1 : A) ⊗ₜ[F] x).map Φ = M.map τ := by
    intro M
    ext a b
    simp [hΦ]
  refine ⟨P.map Φ, ?_, ?_⟩
  · rw [show (P.map Φ).det = Φ P.det from (RingHom.map_det Φ P).symm]
    exact (hP.map Φ).ne_zero
  · rw [← e, h, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, e]
    congr 1
    ext a b
    exact hc _
end CongrOver
end GlobalTheory.HermGlobal
