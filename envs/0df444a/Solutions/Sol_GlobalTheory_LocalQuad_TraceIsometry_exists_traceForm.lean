-- Prove2me | solution 1 for GlobalTheory.LocalQuad.TraceIsometry.exists_traceForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:49:02.872329+00:00
-- url     : https://prove2.me/submissions/17822777-beb4-4cc3-a118-bb8326e7a8b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsOrthogonalBasisDotProductApplyEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_ExistsGlIsometryCompEqOfNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsCongrIffTraceFormsIsometric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open GlobalTheory GlobalTheory.LocalQuad GlobalTheory.LocalQuad.TraceIsometry
open Module
variable {F E : Type*} [Field F] [Field E] [Algebra F E] {c : E →+* E}
namespace GlobalTheory.LocalQuad.TraceIsometry
theorem _root_.solution (hF : ∀ t : E, c t = t ↔ ∃ s : F, algebraMap F E s = t)
    {V : Type*} [AddCommGroup V] [Module E V] [Module F V] [IsScalarTower F E V]
    {B : V →ₗ[E] V →ₛₗ[c] E} (hB : ∀ x y, c (B x y) = B y x) :
    ∃ b : V →ₗ[F] V →ₗ[F] F, ∀ x y, algebraMap F E (b x y) = B x y + B y x := by
  have h : ∀ x y, ∃ s : F, algebraMap F E s = B x y + B y x := fun x y =>
    (hF _).1 (by rw [map_add, hB, hB, add_comm])
  choose b hb using h
  have hi := (algebraMap F E).injective
  have hs : ∀ s : F, c (algebraMap F E s) = algebraMap F E s := fun s => (hF _).2 ⟨s, rfl⟩
  refine ⟨LinearMap.mk₂ F b (fun x x' y => hi ?_) (fun s x y => hi ?_) (fun x y y' => hi ?_)
    (fun s x y => hi ?_), hb⟩
  · simp only [map_add, hb, LinearMap.add_apply]
    ring
  · rw [smul_eq_mul, map_mul, hb, hb, ← algebraMap_smul E s x]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, hs, smul_eq_mul]
    ring
  · simp only [map_add, hb, LinearMap.add_apply]
    ring
  · rw [smul_eq_mul, map_mul, hb, hb, ← algebraMap_smul E s y]
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, hs, smul_eq_mul]
    ring
end GlobalTheory.LocalQuad.TraceIsometry
