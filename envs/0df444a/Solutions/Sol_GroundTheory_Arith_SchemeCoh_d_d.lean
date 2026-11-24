-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.d_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:19.044944+00:00
-- url     : https://prove2.me/submissions/e2e65d22-c183-4f8e-b3b6-396e16ca142f

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero

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
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (n : ℕ) (σ : Cochain P U n) : d P U (n + 1) (d P U n σ) = 0 := by
  have := AlgebraicTopology.AlternatingCofaceMapComplex.d_squared (cechCosimplicial P U) n
  have h2 := congrArg (fun f => f.hom σ) this
  exact h2
end GroundTheory.Arith.SchemeCoh
