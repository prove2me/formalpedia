-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.equation_of_forall_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:10:30.106479+00:00
-- url     : https://prove2.me/submissions/5b2cc6fd-e856-4fc3-8901-8c673660b29a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_AddXYZOrChordXYZOrOriginXYZNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_OverHomEqIffForallIsAlgClosedAlgebra
import Theorems.Thm_GlobalTheory_eq_zero_of_forall_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {A : Type*} [CommRing A]
namespace GlobalTheory.WeierstrassCurve
theorem _root_.solution {A : Type u} [CommRing A] [_root_.IsReduced A]
    {V : WeierstrassCurve A} {P : Fin 3 → A}
    (h : ∀ (k : Type u) [Field k] (φ : A →+* k), (V.map φ).toProjective.Equation (φ ∘ P)) :
    V.toProjective.Equation P := by
  refine eq_zero_of_forall_field fun k _ φ => ?_
  have := h k φ
  change (V.toProjective.map φ).Equation _ at this
  rwa [WeierstrassCurve.Projective.Equation, WeierstrassCurve.Projective.map_polynomial,
    MvPolynomial.eval_map, ← MvPolynomial.eval₂_comp] at this
end GlobalTheory.WeierstrassCurve
