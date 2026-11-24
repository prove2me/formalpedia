-- Prove2me | solution 1 for GlobalTheory.LatPair.glue_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:13:20.920801+00:00
-- url     : https://prove2.me/submissions/daa96da2-eaa9-407e-a184-ecd97735a4a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Theorems.Thm_GlobalTheory_LatPair_Pair_lat_eq

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
theorem _root_.solution (h : IsGlue L e) : (glue h).lat = L ⊔ Submodule.span 𝒪[k] {e} := by
  rw [Pair.lat_eq (glue_hasVal h), glue_ker]
end GlobalTheory.LatPair
