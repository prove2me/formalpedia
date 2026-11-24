-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.upU_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:14.60351+00:00
-- url     : https://prove2.me/submissions/190b73a0-4711-455e-92ab-bb093450de5e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NonarchimedeanLocalFieldSecondCountableT2Space

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Pointwise
open GlobalTheory GlobalTheory.RootExchangeFixed
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.RootExchangeFixed
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (C : Matrix n (Fin c) k)
    (h : ∀ l s, valuation k (C l s) ≤ 1) : upU C ∈ KO k (n ⊕ Fin c) := by
  let C' : Matrix n (Fin c) 𝒪[k] := Matrix.of fun l s => ⟨C l s, h l s⟩
  refine ⟨⟨fromBlocks 1 C' 0 1, fromBlocks 1 (-C') 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [upU, C', Matrix.one_apply, apply_ite (algebraMap 𝒪[k] k)]
  all_goals first | rfl | (split_ifs <;> simp)
end GlobalTheory.RootExchangeFixed
