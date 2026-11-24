-- Prove2me | solution 1 for GlobalTheory.FunObj.symN_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:52:46.566259+00:00
-- url     : https://prove2.me/submissions/2a909d12-1485-480d-82ee-b5b3c9ada272

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSumRowCol
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_FlatTensorVacuum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
open GlobalTheory GlobalTheory.FunObj
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.RootEx
variable (k : Type*) [Field k] (n : Type*) [Fintype n] [DecidableEq n] (c : ℕ)
namespace GlobalTheory.FunObj
theorem _root_.solution (ρ : ℕ) : symN k n (2 * ρ) = N k n (2 * ρ) ρ ⊔ N k n (2 * ρ) (ρ + 1) := by
  rw [symN, show (2 * ρ + 1) / 2 = ρ by omega, show 2 * ρ / 2 + 1 = ρ + 1 by omega]
end GlobalTheory.FunObj
