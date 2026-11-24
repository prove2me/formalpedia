-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.summable_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:24:03.242017+00:00
-- url     : https://prove2.me/submissions/f5319699-d2e8-4d58-b6f2-1968aca97770

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {G : Type} [CommGroup G] (U : Subgroup G) (ω : G →* ℂ)
variable {U ω}
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {B M : Set G} (hB : Summable (cs U ω B)) (h : M ⊆ B) : Summable (cs U ω M) := by
  refine Summable.of_norm_bounded hB.norm fun z => ?_
  exact norm_indicator_le_of_subset h _ _
end GlobalTheory.CMVal.Euler
