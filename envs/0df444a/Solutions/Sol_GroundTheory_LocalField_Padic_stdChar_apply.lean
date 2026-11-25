-- Prove2me | solution 1 for GroundTheory.LocalField.Padic.stdChar_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:38:21.691432+00:00
-- url     : https://prove2.me/submissions/869935c7-d54b-40fd-8a71-1ea1a62552f9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourierTrace
import Definitions.Def_GroundTheory_LocalFields_LocalFourierPadic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory
open scoped NNReal ENNReal
open GroundTheory.LocalField.Padic
variable (p : ℕ) [hp : Fact p.Prime]
namespace GroundTheory.LocalField.Padic
theorem _root_.solution (x : ℚ_[p]) (m : ℤ) (k : ℕ) (h : ‖x - (m : ℚ_[p]) / (p : ℚ_[p]) ^ k‖ ≤ 1) :
    stdChar p x = Real.fourierChar (((m : ℚ) / (p : ℚ) ^ k : ℚ) : ℝ) :=
  stdCharFun_eq p x m k h
end GroundTheory.LocalField.Padic
