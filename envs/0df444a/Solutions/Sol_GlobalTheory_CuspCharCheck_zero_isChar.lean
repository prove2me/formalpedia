-- Prove2me | solution 1 for GlobalTheory.CuspCharCheck.zero_isChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:39:10.062921+00:00
-- url     : https://prove2.me/submissions/3cc4085c-3856-4a9c-be55-c414be2252ae

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_CuspEllipticValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralIdempotentIrreducibleCharacterProps
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_SubgroupCharacterSums_SumSubgroupEqZeroIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CuspElliptic
open GlobalTheory GlobalTheory.CuspCharCheck
variable {G : Type} [Group G]
namespace GlobalTheory.CuspCharCheck
theorem _root_.solution : IsChar (fun _ : G => (0 : ℂ)) := ⟨0, 1, fun _ => by simp⟩
end GlobalTheory.CuspCharCheck
