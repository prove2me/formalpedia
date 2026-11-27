-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.overEquivalence_inverse_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:54.29828+00:00
-- url     : https://prove2.me/submissions/c69f631a-d833-4dbd-a1f5-9ac462c8ed33

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafHOver
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProperCohomology_SheafHEquiv

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
open CategoryTheory Limits Opposite Abelian TopologicalSpace AlgebraicGeometry
universe w' v u
noncomputable section
variable {X : Scheme.{u}} (U : X.Opens)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (W : U.toScheme.Opens) :
    (U.overEquivalence.inverse.obj W).left = U.ι ''ᵁ W := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
end GroundTheory.Arith.SchemeCoh
