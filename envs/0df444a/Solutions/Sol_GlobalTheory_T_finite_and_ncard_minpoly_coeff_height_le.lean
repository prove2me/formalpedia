-- Prove2me | solution 1 for GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:22:04.281307+00:00
-- url     : https://prove2.me/submissions/e8803fa9-d5b8-4a35-b348-1a7e77d4e90b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLe
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FiniteAndNcardMinpolyCoeffHeightLeStatement
import Theorems.Thm_GlobalTheory_MinpolyHeightCount_finite_and_ncard_minpoly_height_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  first | exact @GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | exact GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | (intros; apply GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le <;> assumption)
end _root_.GlobalTheory.T
