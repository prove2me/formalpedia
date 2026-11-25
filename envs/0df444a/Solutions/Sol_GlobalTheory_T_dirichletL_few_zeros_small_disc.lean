-- Prove2me | solution 1 for GlobalTheory.T.dirichletL_few_zeros_small_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:03:23.978812+00:00
-- url     : https://prove2.me/submissions/d82f500e-8a7e-4433-83d6-d829ba8302ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLFewZerosSmallDisc
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLFewZerosSmallDiscStatement
import Theorems.Thm_GlobalTheory_SmallDiscZeros_few_zeros


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
theorem _root_.solution : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t r : ℝ), (χ ≠ 1 ∨ 2 ≤ |t|) → 0 < r → r ≤ 1 / 2 → (zerosDisc χ (1 + t * I) r).Finite ∧ (∑ᶠ w ∈ zerosDisc χ (1 + t * I) r, (ord χ w : ℝ)) ≤ C * (1 + r * Real.log (q * (|t| + 2))) := by
  first | exact @GlobalTheory.SmallDiscZeros.few_zeros | exact GlobalTheory.SmallDiscZeros.few_zeros | (intros; apply GlobalTheory.SmallDiscZeros.few_zeros <;> assumption)
end _root_.GlobalTheory.T
