-- Prove2me | solution 1 for GlobalTheory.classNumber_le_four_mul_abs_discr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:10:47.933807+00:00
-- url     : https://prove2.me/submissions/cfded377-845b-4834-902b-fb2fecc42545

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ClassNumberLeAbsDiscrOfFinrankEqTwo
import Theorems.Thm_GlobalTheory_classNumber_le_abs_discr_of_finrank_eq_two

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (NumberField.classNumber K : ℝ) ≤ 4 * |(NumberField.discr K : ℝ)| := by
  intro K _ _ h
  have := _root_.GlobalTheory.classNumber_le_abs_discr_of_finrank_eq_two K h
  have := abs_nonneg (NumberField.discr K : ℝ)
  linarith
end _root_.GlobalTheory
end GlobalTheory
