-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.reesRingHom_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:13:36.927856+00:00
-- url     : https://prove2.me/submissions/ccfcc2bf-c8d5-431b-b0a8-d131693c9775

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesRing
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_reesInr_comp

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
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (r : reesAlgebra I) :
    reesRingHom hV (reesInr I V r) = (r : Polynomial A).map (algV X V) := by
  have := congrArg (fun f : CommRingCat.of (reesAlgebra I) ⟶ polyRing I V => f.hom r)
    (reesInr_comp (I := I) hV)
  change polyRingHom hV (((reesInr I V ≫ (reesPolyMap I X).app _)).hom r) = _
  rw [this]
  exact polyRingHom_inr hV _
end GroundTheory.Arith.SchemeCoh
