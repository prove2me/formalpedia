-- Prove2me | solution 1 for GlobalTheory.LatPair.Pair.HasVal.gl_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:13:45.400182+00:00
-- url     : https://prove2.me/submissions/108a7be7-dd5d-40f5-b426-b431f1d51147

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
variable [Fintype n] [DecidableEq n]
open GlobalTheory.LatPair.Pair
namespace GlobalTheory.LatPair.Pair
namespace HasVal
theorem _root_.solution {P : Pair k n} {x : n → k} {a : 𝓀[k]} (h : P.HasVal x a) (g : GL n k) :
    (g • P).HasVal (g • x) a := smul_hasVal.2 (by simpa using h)
end HasVal
end GlobalTheory.LatPair.Pair
