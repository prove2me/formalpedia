-- Prove2me | solution 1 for GlobalTheory.StepData.normalBasis_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:02.579776+00:00
-- url     : https://prove2.me/submissions/a97c9b94-f566-45fe-bb9b-585bbe9464b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ValuationDetOfMemKO
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock

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
theorem _root_.solution (ϖ : kˣ) (e : Fin c → ℤ) (z : n → k) : (normalBasis ϖ e z).val =
    fromBlocks 1 (Matrix.of fun r i => if i.val = 0 then z r * (ϖ : k) ^ e i else 0) 0
      (diagonal fun i => (ϖ : k) ^ e i) := by
  change fromBlocks 1 _ 0 1 * fromBlocks 1 0 0 (diagonal _) = _
  rw [fromBlocks_multiply]
  ext (r | r) (i | i) <;> simp
end GlobalTheory.StepData
