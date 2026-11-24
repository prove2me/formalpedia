-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.bd_bd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:35.987972+00:00
-- url     : https://prove2.me/submissions/ff9d93f9-a566-4954-9023-c0a98caaee71

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechNaturality_Chains

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
open CategoryTheory
universe w
variable {ι : Type w}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (n : ℕ) (c : Chain ι (n + 2)) : bd n (bd (n + 1) c) = 0 := by
  have := AlgebraicTopology.AlternatingFaceMapComplex.d_squared (chainSimplicial ι) n
  exact congrArg (fun f => f.hom c) this
end GroundTheory.Arith.SchemeCoh
