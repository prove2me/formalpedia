-- Prove2me | solution 1 for GlobalTheory.StepData.mem_latOf_typeFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:04:11.187473+00:00
-- url     : https://prove2.me/submissions/c78dbef4-d48b-46e1-9000-ce2330e170ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_mem_latOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.StepData
open GlobalTheory.SplitWeil GlobalTheory.RootEx
variable {k : Type*} [Field k] {ι n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
namespace GlobalTheory.StepData
theorem _root_.solution [ValuativeRel k] (ϖ : kˣ) (ord : ι ≃ n ⊕ Fin c) (y : n ⊕ Fin c → k) :
    y ∈ latOf (typeFrame ϖ ord).bas ↔ (∀ i, y (.inl i) ∈ 𝒪[k]) ∧
      ∀ i : Fin c, valuation k (y (.inr i)) ≤ valuation k ((ϖ : k) ^ (i.val + 1)) := by
  have e : ((typeFrame ϖ ord).bas⁻¹).val = fromBlocks 1 0 0 (diagonal fun i : Fin c => ((ϖ : k) ^ (i.val + 1))⁻¹) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    change fromBlocks 1 0 0 (diagonal _) * _ = _
    simp [fromBlocks_multiply, diagonal_mul_diagonal]
  rw [mem_latOf, e, Sum.forall, fromBlocks_mulVec]
  refine and_congr (by simp) (forall_congr' fun i => ?_)
  have : 0 < valuation k ((ϖ : k) ^ (i.val + 1)) := by simp [zero_lt_iff]
  simp only [zero_mulVec, zero_add, Sum.elim_inr, mulVec_diagonal, Valuation.mem_integer_iff, map_mul, map_inv₀,
    Function.comp]
  rw [inv_mul_le_one₀ this]
end GlobalTheory.StepData
