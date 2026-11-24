-- Prove2me | solution 1 for GlobalTheory.HermLocal.CongrOver.det_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:48:13.1703+00:00
-- url     : https://prove2.me/submissions/d5a04972-0531-44d3-95d7-0ab5a212985d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometricCm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasseNormTheoremQuadraticExtension
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_UnimodUnramUnique
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Theorems.Thm_GlobalTheory_LocalQuad_HermClass_Congr_det


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
theorem _root_.solution (hd' : G'.det ≠ 0) (h : CongrOver A G G') :
    ∃ z : A ⊗[maximalRealSubfield E] E,
      (1 : A) ⊗ₜ[maximalRealSubfield E] (G.det / G'.det) = z * ccBase E A z := by
  obtain ⟨P, ⟨p, hp⟩, h⟩ := h
  let ι : E →+* A ⊗[maximalRealSubfield E] E := Algebra.TensorProduct.includeRight.toRingHom
  have h1 : ι G'.det = p * ι G.det * ccBase E A p := by
    rw [RingHom.map_det, RingHom.map_det, hp, AlgHom.map_det, ← Matrix.det_transpose P,
      ← Matrix.det_mul, ← Matrix.det_mul]
    exact congrArg Matrix.det h
  have h2 : ι (G.det / G'.det) * ι G'.det = ι G.det := by rw [← map_mul, div_mul_cancel₀ _ hd']
  have h3 : ccBase E A p * ccBase E A (p⁻¹ : (A ⊗[maximalRealSubfield E] E)ˣ) = 1 := by
    rw [← map_mul, p.mul_inv, map_one]
  refine ⟨(p⁻¹ : (A ⊗[maximalRealSubfield E] E)ˣ), ?_⟩
  change ι (G.det / G'.det) = _
  refine ((hd'.isUnit.map ι).mul_left_inj).1 ?_
  rw [h2, h1]
  linear_combination (-ι G.det) * p.mul_inv - (p * (p⁻¹ : (A ⊗[maximalRealSubfield E] E)ˣ) * ι G.det) * h3
end CongrOver
end GlobalTheory.HermLocal
