-- Prove2me | solution 1 for GlobalTheory.isLocalHom_of_factor_stalk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:04:55.456933+00:00
-- url     : https://prove2.me/submissions/09ac80b9-e23d-4a0f-9aef-7c7b59f990de

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Theorems.Thm_GlobalTheory_existsUnique_factor_stalk

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
theorem _root_.solution {f : Spec (.of R) ⟶ X} {x : X} (hx : f (closedPoint R) = x)
    {φ : X.presheaf.stalk x ⟶ .of R} (hφ : Spec.map φ ≫ X.fromSpecStalk x = f) :
    IsLocalHom φ.hom := by
  subst hx
  rw [(existsUnique_factor_stalk f rfl).unique hφ
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) f)]
  exact Scheme.isLocalHom_stalkClosedPointTo' f
end GlobalTheory
