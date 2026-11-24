-- Prove2me | solution 1 for GlobalTheory.HermGlobal.CongrOver.of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:38:41.210158+00:00
-- url     : https://prove2.me/submissions/b205a1e0-83fb-466e-b4aa-dfbc4c533caf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution
    (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map σ) :
    CongrOver σ A G G' := by
  obtain ⟨P, hP, rfl⟩ := h
  let ι : E →+* A ⊗[F] E := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨P.map ι, ?_, ?_⟩
  · rw [show (P.map ι).det = ι P.det from (RingHom.map_det ι P).symm]
    exact hP.isUnit.map ι
  · change (Pᵀ * G * P.map σ).map ι = (P.map ι)ᵀ * G.map ι * _
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    rfl
end CongrOver
end GlobalTheory.HermGlobal
