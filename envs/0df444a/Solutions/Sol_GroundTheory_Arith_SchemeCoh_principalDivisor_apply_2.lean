-- Prove2me | solution 2 for GroundTheory.Arith.SchemeCoh.principalDivisor_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:42:57.026249+00:00
-- url     : https://prove2.me/submissions/d7f97731-90df-4608-8002-1d9c71ab2809

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor

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
open CategoryTheory AlgebraicGeometry IsDedekindDomain TopologicalSpace Topology
universe u
variable {X : Scheme.{u}}
variable [IsIntegral X] [IsNoetherian X] [IsNormalScheme X]
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (f : (X.functionField)ˣ) (x : PrimeDivisor X) :
    principalDivisor (Additive.ofMul f) x = x.ord (f : X.functionField) := rfl
end GroundTheory.Arith.SchemeCoh
