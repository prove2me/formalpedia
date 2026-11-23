-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.KAlg.coord_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:22.424255+00:00
-- url     : https://prove2.me/submissions/8ea5cc72-6b71-4363-9390-3cfa7cb7079c

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.KAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R : Type} [CommRing R] [Algebra F R]
namespace GlobalTheory.CompanionTheory.SW.KAlg
theorem _root_.solution (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    {a c a' c' : R} (h : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ = a' ⊗ₜ[F] (1 : E) + c' ⊗ₜ[F] δ) :
    a = a' ∧ c = c' := by
  let B := Algebra.TensorProduct.basis R b
  have e : ∀ p q : R, p ⊗ₜ[F] (1 : E) + q ⊗ₜ[F] δ = p • B 0 + q • B 1 := by
    intro p q
    have e0 : B 0 = (1 : R) ⊗ₜ[F] (1 : E) := by simp [B, hb0]
    have e1 : B 1 = (1 : R) ⊗ₜ[F] δ := by simp [B, hb1]
    rw [e0, e1, TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    simp
  rw [e, e] at h
  have h0 := congrArg (fun y => B.repr y 0) h
  have h1 := congrArg (fun y => B.repr y 1) h
  simp at h0 h1
  exact ⟨h0, h1⟩
end GlobalTheory.CompanionTheory.SW.KAlg
