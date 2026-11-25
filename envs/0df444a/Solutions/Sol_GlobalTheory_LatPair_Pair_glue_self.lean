-- Prove2me | solution 1 for GlobalTheory.LatPair.Pair.glue_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:04:32.018001+00:00
-- url     : https://prove2.me/submissions/77fe827d-2acb-4920-b862-bed6f1c691b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_eq_glue_iff

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
variable {L L' : Submodule 𝒪[k] (n → k)} {e e' : n → k}
namespace GlobalTheory.LatPair
namespace Pair
theorem _root_.solution {P : Pair k n} (he : P.HasVal e 1) : glue (Pair.isGlue he) = P :=
  ((eq_glue_iff _).2 ⟨rfl, he⟩).symm
end Pair
end GlobalTheory.LatPair
