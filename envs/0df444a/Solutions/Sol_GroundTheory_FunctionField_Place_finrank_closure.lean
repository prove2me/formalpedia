-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.finrank_closure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:24:07.898457+00:00
-- url     : https://prove2.me/submissions/e852ba76-1205-4c01-9785-31360ee27806

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove
import Definitions.Def_GroundTheory_FunctionField_PlaceSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
attribute [local instance low] algebraExt
attribute [local instance] isScalarTower_ext
attribute [local instance] isTorsionFree_ext
variable [IsFunctionField k K] [FiniteDimensional K K'] [Algebra.IsSeparable K K'] (v : Place k K)
omit [Algebra k K'] [IsScalarTower k K K']
namespace GroundTheory.FunctionField.Place
theorem _root_.solution :
    Module.finrank v.ring (integralClosure v.ring K') = Module.finrank K K' :=
  IsIntegralClosure.rank v.ring K K' _
end GroundTheory.FunctionField.Place
