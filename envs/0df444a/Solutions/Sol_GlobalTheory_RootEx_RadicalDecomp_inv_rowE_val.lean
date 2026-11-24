-- Prove2me | solution 1 for GlobalTheory.RootEx.RadicalDecomp.inv_rowE_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:03:14.795358+00:00
-- url     : https://prove2.me/submissions/17e7a03a-0346-4b4a-af85-59bfc5ec32a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentSubgroupSuccDecomposition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RadicalDecomp
open GlobalTheory.RootEx.Radical
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c p : ℕ}
namespace GlobalTheory.RootEx.RadicalDecomp
theorem _root_.solution (u : n → k) : ((rowE c p u)⁻¹).val =
    fromBlocks 1 0 (-(Matrix.of fun (l : Fin c) s => if l.val + 1 = p then u s else 0)) 1 := rfl
end GlobalTheory.RootEx.RadicalDecomp
