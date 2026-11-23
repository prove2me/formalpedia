-- Prove2me | solution 1 for GlobalTheory.LocalQuad.TraceIsometry.trace_eq_of_apply_self_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:45.323295+00:00
-- url     : https://prove2.me/submissions/4f51f1f4-806d-4d75-b0c7-2210a00bc55b

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
theorem _root_.solution {V W : Type*} [AddCommGroup V] [Module E V] [AddCommGroup W]
    [Module E W] {B : V →ₗ[E] V →ₛₗ[c] E} {B' : W →ₗ[E] W →ₛₗ[c] E} {φ : V → W}
    (hadd : ∀ x y, φ (x + y) = φ x + φ y) (hφ : ∀ x, B' (φ x) (φ x) = B x x) (x y : V) :
    B' (φ x) (φ y) + B' (φ y) (φ x) = B x y + B y x := by
  have h := hφ (x + y)
  rw [hadd] at h
  simp only [map_add, LinearMap.add_apply, hφ] at h
  linear_combination h
end GlobalTheory.LocalQuad.TraceIsometry
