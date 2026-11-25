-- Prove2me | solution 1 for GlobalTheory.WeierstrassCurve.IsSumTriple.equiv_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:47.855598+00:00
-- url     : https://prove2.me/submissions/0a683b2e-00bd-4e03-8cf1-3ff8e64cd2dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsStandardSmoothOfRelativeDimensionAwayJacobian
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Theorems.Thm_GlobalTheory_AddLaw_equiv_add_of_proportional


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open HomogeneousIdeal
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
open AddLaw
variable {A B : Type*} [CommRing A] [CommRing B]
variable {V : WeierstrassCurve A} {P Q T : Fin 3 → A}
open WeierstrassCurve.Projective
namespace GlobalTheory.WeierstrassCurve
namespace IsSumTriple
theorem _root_.solution {k : Type*} [Field k] {V : WeierstrassCurve k} {P Q T : Fin 3 → k}
    (h : IsSumTriple V P Q T) (hP : V.toProjective.Nonsingular P)
    (hQ : V.toProjective.Nonsingular Q) (hT : T ≠ 0) : T ≈ V.toProjective.add P Q :=
  equiv_add_of_proportional hP hQ h.add h.diag hT
end IsSumTriple
end GlobalTheory.WeierstrassCurve
