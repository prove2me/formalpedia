-- Prove2me | solution 1 for GlobalTheory.LocalQuad.exists_congr_iff_trace_forms_isometric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:45:10.669431+00:00
-- url     : https://prove2.me/submissions/509eb88d-f7e4-42cd-9b54-fdff60501f8b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric
import Theorems.Thm_GlobalTheory_LocalQuad_TraceIsometry_exists_linearMap_isometry
import Theorems.Thm_GlobalTheory_HermDiag_map_dotProduct_mulVec_comp
import Theorems.Thm_GlobalTheory_HermWitt_dotProduct_congr_mulVec
import Theorems.Thm_P2M_GlobalTheory_HermDiag_toLinearMap_____eq_dotProduct_72a26b3ab9da


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
namespace GlobalTheory.LocalQuad
theorem _root_.solution {F E : Type*} [Field F] [Field E]
    [Algebra F E] (h2 : (2 : E) ≠ 0) (c : E →+* E) (hc : ∀ t, c (c t) = t)
    (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {n : Type*} [Fintype n] [DecidableEq n] {G G' : Matrix n n E}
    (hG : ∀ a b, c (G a b) = G b a) (hG' : ∀ a b, c (G' a b) = G' b a)
    (hd : G.det ≠ 0) (hd' : G'.det ≠ 0) :
    (∃ P : Matrix n n E, P.det ≠ 0 ∧ G' = Pᵀ * G * P.map c) ↔
      ∃ φ : (n → E) ≃ₗ[F] (n → E),
        ∀ x, x ⬝ᵥ G' *ᵥ (c ∘ x) = φ x ⬝ᵥ G *ᵥ (c ∘ φ x) := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨(Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP.isUnit)).restrictScalars F,
      fun x => ?_⟩
    rw [GlobalTheory.HermWitt.dotProduct_congr_mulVec]
    rfl
  · rintro ⟨φ, hφ⟩
    obtain ⟨ψ, hψ⟩ := TraceIsometry.exists_linearMap_isometry h2 hc hF _
      (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G')
      (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c G)
      (fun x y => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
          GlobalTheory.HermDiag.map_dotProduct_mulVec_comp hc hG'])
      (fun x y => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
          GlobalTheory.HermDiag.map_dotProduct_mulVec_comp hc hG])
      rfl φ.toLinearMap
      (fun x => by
        simp only [GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct]
        exact (hφ x).symm)
    have h : G' = (LinearMap.toMatrix' ψ)ᵀ * G * (LinearMap.toMatrix' ψ).map c := by
      apply (Matrix.toLinearMapₛₗ₂' E (RingHom.id E) c).injective
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      rw [← hψ, GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct,
        GlobalTheory.HermDiag.toLinearMapₛₗ₂'_eq_dotProduct, GlobalTheory.HermWitt.dotProduct_congr_mulVec,
        LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    refine ⟨_, fun h0 => hd' ?_, h⟩
    rw [h, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
end GlobalTheory.LocalQuad
