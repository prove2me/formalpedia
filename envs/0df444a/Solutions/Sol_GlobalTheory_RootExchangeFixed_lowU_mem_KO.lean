-- Prove2me | solution 1 for GlobalTheory.RootExchangeFixed.lowU_mem_KO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:11.752802+00:00
-- url     : https://prove2.me/submissions/8a887b21-d368-4c33-b04e-28b5d7b927be

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
theorem _root_.solution {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (C : Matrix (Fin c) n k)
    (h : ∀ l s, valuation k (C l s) ≤ 1) : lowU C ∈ KO k (n ⊕ Fin c) := by
  let C' : Matrix (Fin c) n 𝒪[k] := Matrix.of fun l s => ⟨C l s, h l s⟩
  refine ⟨⟨fromBlocks 1 0 C' 1, fromBlocks 1 0 (-C') 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩, ?_⟩
  ext r s
  rcases r with r | r <;> rcases s with s | s <;>
    simp [lowU, C', Matrix.one_apply, apply_ite (algebraMap 𝒪[k] k)]
  all_goals first | rfl | (split_ifs <;> simp)
end GlobalTheory.RootExchangeFixed
