-- Prove2me | solution 1 for GroundTheory.FunctionField.Place.liesOver_comap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:47:44.462574+00:00
-- url     : https://prove2.me/submissions/929b9192-a49c-42e1-be48-439171f61fc8

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
theorem _root_.solution [Algebra.IsAlgebraic K K'] (w : Place k K') : w.LiesOver (w.comap (K := K)) :=
  rfl
end GroundTheory.FunctionField.Place
