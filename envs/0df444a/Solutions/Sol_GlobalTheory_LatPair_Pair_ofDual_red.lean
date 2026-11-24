-- Prove2me | solution 1 for GlobalTheory.LatPair.Pair.ofDual_red
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:37:34.082411+00:00
-- url     : https://prove2.me/submissions/abfdb7d9-8cff-4c28-a410-9cec9b7bb3ac

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
variable (L : Submodule 𝒪[k] (n → k)) [hL : L.IsLattice k]
namespace GlobalTheory.LatPair
namespace Pair
theorem _root_.solution (P : Pair k n) : ofDual P.lat ⟨P.red, P.red_ne⟩ = P := rfl
end Pair
end GlobalTheory.LatPair
