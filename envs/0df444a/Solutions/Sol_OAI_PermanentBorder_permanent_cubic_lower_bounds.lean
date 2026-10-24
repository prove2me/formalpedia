-- Prove2me | solution 1 for OAI.PermanentBorder.permanent_cubic_lower_bounds
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:52:11.86972+00:00
-- url     : https://prove2.me/submissions/4b07582c-a0df-41af-a0c5-ed48edf24c80

import Mathlib
import Definitions.Def_PermanentCubic
import Theorems.Thm_OAI_PermanentBorder_permanent_border_cubic_lower_bound
import Theorems.Thm_OAI_PermanentBorder_permanent_exact_cubic_lower_bound

section
-- module Solutions.OAIQW_PermanentBorder.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder
open MvPolynomial

theorem permanent_cubic_lower_bounds_oai :
    (∀ (m n : ℕ), 1408 ≤ m → HasBorderDeterminant n (permanentPolynomial m) →
      (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ)) ∧
    (∀ (m n : ℕ), 1408 ≤ m → HasExactDeterminant n (permanentPolynomial m) →
      (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ)) :=
  ⟨permanent_border_cubic_lower_bound, permanent_exact_cubic_lower_bound⟩

end PermanentBorder

end OAI
end

theorem solution : type_of% @OAI.PermanentBorder.permanent_cubic_lower_bounds_oai := @OAI.PermanentBorder.permanent_cubic_lower_bounds_oai
