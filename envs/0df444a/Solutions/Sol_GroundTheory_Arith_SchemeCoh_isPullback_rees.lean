-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isPullback_rees
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:02:00.265878+00:00
-- url     : https://prove2.me/submissions/7c050223-a7de-4b06-80b9-e62cb357ab45

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
    IsPullback (reesPr I X) (reesSnd I X) (X ↘ Spec (.of A)) (reesStructure I) :=
  IsPullback.of_hasPullback _ _
end GroundTheory.Arith.SchemeCoh
