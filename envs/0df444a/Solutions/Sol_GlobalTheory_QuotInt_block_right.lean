-- Prove2me | solution 1 for GlobalTheory.QuotInt.block_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:51:58.788633+00:00
-- url     : https://prove2.me/submissions/e03ddb8c-e086-42f3-8455-5916de810b9f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IsMulLeftInvariantVolGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeUnipotentHaarAndModulusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QuotientIntegralParabolicUnfolding
import Theorems.Thm_GlobalTheory_QuotInt_block_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.QuotInt
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ}
omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.QuotInt
theorem _root_.solution (x : GL n k) {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c p) :
    (u * embX c x).val.toBlocks₁₁ = x.val := by
  have h := block_of_mem hu
  change (u.val * fromBlocks x.val 0 0 1).toBlocks₁₁ = _
  rw [← fromBlocks_toBlocks u.val, fromBlocks_multiply, h]
  simp
end GlobalTheory.QuotInt
