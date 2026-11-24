-- Prove2me | solution 1 for GlobalTheory.LatPair.phiOne_mem_SB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:54:39.814436+00:00
-- url     : https://prove2.me/submissions/73c2038e-b306-4541-84f7-92c83b2fab2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsClopenIsCompactMapsPair
import Theorems.Thm_GlobalTheory_LatPair_ite_mem_SB
import Theorems.Thm_GlobalTheory_LatPair_isClopen_isCompact_mapsPair

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
open SplitWeil
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n] [Fintype n']
namespace GlobalTheory.LatPair
theorem _root_.solution (P : Pair k n') (Q : Pair k n) : phiOne P Q ∈ SB (Matrix n n' k) := by
  classical
  exact ite_mem_SB (isClopen_isCompact_mapsPair P Q).1 (isClopen_isCompact_mapsPair P Q).2
end GlobalTheory.LatPair
