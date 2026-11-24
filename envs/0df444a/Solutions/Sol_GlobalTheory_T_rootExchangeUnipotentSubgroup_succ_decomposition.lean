-- Prove2me | solution 1 for GlobalTheory.T.rootExchangeUnipotentSubgroup_succ_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:22:21.346397+00:00
-- url     : https://prove2.me/submissions/2efa8e76-6602-4c14-905b-849315fec259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecomposition
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecompositionStatement
import Theorems.Thm_GlobalTheory_RootEx_RadicalDecomp_succ_decomp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), ∀ g ∈ N k n c (p + 1), ∃ g₁ ∈ N k n c p ⊓ N k n c (p + 1), ∃ u : n → k, g = g₁ * rowE c p u := by
  first | exact @GlobalTheory.RootEx.RadicalDecomp.succ_decomp | exact GlobalTheory.RootEx.RadicalDecomp.succ_decomp | (intros; apply GlobalTheory.RootEx.RadicalDecomp.succ_decomp <;> assumption)
end _root_.GlobalTheory.T
