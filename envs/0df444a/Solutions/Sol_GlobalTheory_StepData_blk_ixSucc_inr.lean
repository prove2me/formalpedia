-- Prove2me | solution 1 for GlobalTheory.StepData.blk_ixSucc_inr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:10.025127+00:00
-- url     : https://prove2.me/submissions/a4026efa-8252-4935-8c45-91b386a28e16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IterPrincipalSpec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.StepData ValuativeRel Matrix
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
namespace GlobalTheory.StepData
theorem _root_.solution {j : ℕ} (s : t) : (ixSucc r t j (.inr s)).blk = j + 1 := rfl
end GlobalTheory.StepData
