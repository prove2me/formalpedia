-- Prove2me | solution 1 for GlobalTheory.Nef.Lib.ord_toRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:15.109723+00:00
-- url     : https://prove2.me/submissions/272be625-a077-4706-afef-cde23f3ec433

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped IntermediateField Polynomial
open GlobalTheory GlobalTheory.Nef
variable {k F : Type} [Field k] [Field F] [Algebra k F]
open GlobalTheory.Nef.Lib
open scoped WithZero
open IsDedekindDomain GroundTheory.FunctionField
namespace GlobalTheory.Nef.Lib
theorem _root_.solution [IsFunctionField k F] (v : Nef.Place k F) (x : F) : (toRing v).ord x = ord v x := by
  rw [GroundTheory.FunctionField.Place.ord, valuation_toRing, ord]
end GlobalTheory.Nef.Lib
