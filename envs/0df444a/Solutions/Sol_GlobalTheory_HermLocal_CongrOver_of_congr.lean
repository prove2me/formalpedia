-- Prove2me | solution 1 for GlobalTheory.HermLocal.CongrOver.of_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:59:29.464779+00:00
-- url     : https://prove2.me/submissions/775c0589-25e9-4057-81b2-13c7ee5e525b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
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
open scoped Matrix TensorProduct ComplexConjugate WithZero
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermLocal
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
namespace GlobalTheory.HermLocal
namespace CongrOver
theorem _root_.solution
    (h : ∃ P : Matrix (Fin r) (Fin r) E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map cc) :
    CongrOver A G G' := by
  obtain ⟨P, hP, rfl⟩ := h
  let ι : E →+* A ⊗[maximalRealSubfield E] E := Algebra.TensorProduct.includeRight.toRingHom
  refine ⟨P.map ι, ?_, ?_⟩
  · rw [show (P.map ι).det = ι P.det from (RingHom.map_det ι P).symm]
    exact hP.isUnit.map ι
  · change (Pᵀ * G * P.map cc).map ι = (P.map ι)ᵀ * G.map ι * _
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    rfl
end CongrOver
end GlobalTheory.HermLocal
