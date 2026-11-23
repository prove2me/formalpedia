-- Prove2me | solution 1 for GlobalTheory.LatPair.Pair.hasVal_ev
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:46.235374+00:00
-- url     : https://prove2.me/submissions/ce0be492-1aa0-4819-8880-45b4c9b99b8a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv

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
theorem _root_.solution {P : Pair k n} {x : n → k} (h : x ∈ P.lat) : P.HasVal x (P.ev x) := ⟨h, by simp [ev, h]⟩
end GlobalTheory.LatPair.Pair
