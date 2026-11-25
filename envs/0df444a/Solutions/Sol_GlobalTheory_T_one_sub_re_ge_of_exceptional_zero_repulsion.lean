-- Prove2me | solution 1 for GlobalTheory.T.one_sub_re_ge_of_exceptional_zero_repulsion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:10:26.780927+00:00
-- url     : https://prove2.me/submissions/a638c028-93e9-4080-aaa4-ad0eb366295f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RepulsionStatement
import Theorems.Thm_GlobalTheory_Lin_Repulsion_repulsion


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
theorem _root_.solution : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (β L : ℝ) (ρ : ℂ), χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β < 1 → 1 / 2 ≤ β → LFunction χ₁ β = 0 → LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re < 1 → (χ ≠ χ₁ ∨ ρ ≠ β ∨ 2 ≤ ord χ₁ β) → Real.log (q * (|ρ.im| + 2)) ≤ L → c * Real.log (c / ((1 - β) * L)) / L ≤ 1 - ρ.re := by
  first | exact @GlobalTheory.Lin.Repulsion.repulsion | exact GlobalTheory.Lin.Repulsion.repulsion | (intros; apply GlobalTheory.Lin.Repulsion.repulsion <;> assumption)
end _root_.GlobalTheory.T
