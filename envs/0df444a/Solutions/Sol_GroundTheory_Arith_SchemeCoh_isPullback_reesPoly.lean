-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isPullback_reesPoly
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:00.393203+00:00
-- url     : https://prove2.me/submissions/ddf72e45-7427-446b-b39b-36780db3978e

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesSubmodule
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_PullbackGamma
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_ReesScheme

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
variable {A : Type u} [CommRing A] (I : Ideal A) (X : Scheme.{u}) [X.Over (Spec (.of A))]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution :
    IsPullback (reesPolyMap I X) (reesPolySnd I X) (reesSnd I X) (reesPolyStructure I) :=
  IsPullback.of_hasPullback _ _
end GroundTheory.Arith.SchemeCoh
