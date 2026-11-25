-- Prove2me | solution 1 for GlobalTheory.LatPair.Pair.HasVal.ev_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:04:29.291295+00:00
-- url     : https://prove2.me/submissions/839ea4da-3821-4255-8475-c975d74cd9ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_Pair_hasVal_ev

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
open GlobalTheory GlobalTheory.LatPair
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {n n' : Type*}
open GlobalTheory.LatPair.Pair
namespace GlobalTheory.LatPair.Pair
namespace HasVal
theorem _root_.solution {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) : P.ev x = a :=
  (hasVal_ev h.mem).unique h
end HasVal
end GlobalTheory.LatPair.Pair
