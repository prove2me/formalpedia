-- Prove2me | solution 1 for GlobalTheory.HermGlobal.CongrOver.det_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:28:43.442109+00:00
-- url     : https://prove2.me/submissions/e439561c-77a6-420a-afce-1e6c3f7cd156

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_ExistsOrthonormalOfUnimodular
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_HermitianHassePrincipleHolds
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
open scoped Matrix TensorProduct ComplexConjugate
open GlobalTheory.LocalQuad GlobalTheory.LocalQuad.HermClass
open GlobalTheory GlobalTheory.HermGlobal
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
variable {σ : E ≃ₐ[F] E} {A : Type*} [CommRing A] [Algebra F A] {r : ℕ}
  {G G' : Matrix (Fin r) (Fin r) E}
namespace GlobalTheory.HermGlobal
namespace CongrOver
theorem _root_.solution (hd' : G'.det ≠ 0) (h : CongrOver σ A G G') :
    ∃ z : A ⊗[F] E, (1 : A) ⊗ₜ[F] (G.det / G'.det) = z * baseConj σ A z := by
  obtain ⟨P, ⟨p, hp⟩, h⟩ := h
  let ι : E →+* A ⊗[F] E := Algebra.TensorProduct.includeRight.toRingHom
  have h1 : ι G'.det = p * ι G.det * baseConj σ A p := by
    rw [RingHom.map_det, RingHom.map_det, hp, AlgHom.map_det, ← Matrix.det_transpose P,
      ← Matrix.det_mul, ← Matrix.det_mul]
    exact congrArg Matrix.det h
  have h2 : ι (G.det / G'.det) * ι G'.det = ι G.det := by rw [← map_mul, div_mul_cancel₀ _ hd']
  have h3 : baseConj σ A p * baseConj σ A (p⁻¹ : (A ⊗[F] E)ˣ) = 1 := by
    rw [← map_mul, p.mul_inv, map_one]
  refine ⟨(p⁻¹ : (A ⊗[F] E)ˣ), ?_⟩
  change ι (G.det / G'.det) = _
  refine ((hd'.isUnit.map ι).mul_left_inj).1 ?_
  rw [h2, h1]
  linear_combination (-ι G.det) * p.mul_inv - (p * (p⁻¹ : (A ⊗[F] E)ˣ) * ι G.det) * h3
end CongrOver
end GlobalTheory.HermGlobal
