-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.reesInr_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:04:21.355475+00:00
-- url     : https://prove2.me/submissions/960e2051-7c9f-43ad-92e4-92e8eab8905f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesRing
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPullback_reesPoly
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isPushout_app_of_isPullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry CategoryTheory Limits Opposite
universe u
noncomputable section
variable {A : Type u} [CommRing A] {I : Ideal A} {X : Scheme.{u}} [X.Over (Spec (.of A))]
  {V : X.Opens} (hV : IsAffineOpen V)
include hV
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution :
    reesInr I V ≫ (reesPolyMap I X).app _ =
      CommRingCat.ofHom (algebraMap (reesAlgebra I) (Polynomial A)) ≫ polyInr I V := by
  have hw := (isPushout_app_of_isPullback (isPullback_reesPoly I X) (hV.preimage (reesPr I X))).w
  rw [reesInr, polyInr, Category.assoc, hw, ← Category.assoc, ← Category.assoc,
    Scheme.ΓSpecIso_inv_naturality]
end GroundTheory.Arith.SchemeCoh
