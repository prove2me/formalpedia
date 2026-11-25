-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.liesOver_iff_comap_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:05:18.797014+00:00
-- url     : https://prove2.me/submissions/df976cde-a784-4231-b093-173b314d937c

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBasic
import Definitions.Def_GroundTheory_FunctionField_PlaceAbove

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open GroundTheory.FunctionField.Place
variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']
namespace GroundTheory.FunctionField.Place
theorem _root_.solution [Algebra.IsAlgebraic K K'] {w : Place k K'} {v : Place k K} :
    w.LiesOver v ↔ w.comap = v :=
  ⟨fun h => Place.ext h, fun h => congrArg Place.ring h⟩
end GroundTheory.FunctionField.Place
