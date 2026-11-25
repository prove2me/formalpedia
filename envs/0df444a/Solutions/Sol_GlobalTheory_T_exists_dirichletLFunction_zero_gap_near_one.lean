-- Prove2me | solution 1 for GlobalTheory.T.exists_dirichletLFunction_zero_gap_near_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:37:02.43638+00:00
-- url     : https://prove2.me/submissions/37f9abfd-9d82-4d4c-9f20-5098d73e5501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOne
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsDirichletLFunctionZeroGapNearOneStatement
import Theorems.Thm_GlobalTheory_ZeroGapNearOne_exists_gap


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (ρ : ℂ), (χ ≠ 1 ∨ ρ ≠ 1) → LFunction χ ρ = 0 → |ρ.im| ≤ 1 → c / ((q : ℝ) ^ 2 * Real.log (3 * q)) ≤ 1 - ρ.re := by
  first | exact @GlobalTheory.ZeroGapNearOne.exists_gap | exact GlobalTheory.ZeroGapNearOne.exists_gap | (intros; apply GlobalTheory.ZeroGapNearOne.exists_gap <;> assumption)
end _root_.GlobalTheory.T
