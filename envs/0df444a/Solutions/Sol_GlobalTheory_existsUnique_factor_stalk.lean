-- Prove2me | solution 1 for GlobalTheory.existsUnique_factor_stalk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:32.398083+00:00
-- url     : https://prove2.me/submissions/e9e31e34-c98b-4f7f-920c-5143198cdb99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {R : Type u} [CommRing R] [IsLocalRing R] {X : Scheme.{u}}
namespace GlobalTheory
theorem _root_.solution (f : Spec (.of R) ⟶ X) {x : X} (hx : f (closedPoint R) = x) :
    ∃! φ : X.presheaf.stalk x ⟶ .of R, Spec.map φ ≫ X.fromSpecStalk x = f := by
  subst hx
  refine ⟨Scheme.stalkClosedPointTo (R := .of R) f,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) f, fun φ hφ => ?_⟩
  apply Spec.map_injective
  rw [← cancel_mono (X.fromSpecStalk _), hφ]
  exact (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) f).symm
end GlobalTheory
