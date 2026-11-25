-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.isEmpty_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:00:21.473165+00:00
-- url     : https://prove2.me/submissions/70e05589-7d3b-47e0-9982-d64b7e39cdb4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
namespace GlobalTheory.LatPair.Model
theorem _root_.solution [IsEmpty n] : IsEmpty (Pair k n) :=
  ⟨fun P => P.fn_ne (LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero])⟩
end GlobalTheory.LatPair.Model
