-- Prove2me | solution 1 for OAI.PermanentBorder.permanent_exact_cubic_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T19:52:12.787239+00:00
-- url     : https://prove2.me/submissions/c473141c-e4c0-4aa0-b186-e4a85c6b5e84

import Mathlib
import Definitions.Def_PermanentCubic
import Theorems.Thm_OAI_PermanentBorder_permanent_border_cubic_lower_bound

section
-- module Solutions.OAIQW_PermanentBorder.Model
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder

open Filter
open scoped Topology

theorem HasExactDeterminant.hasBorderDeterminant {σ : Type*} [Fintype σ]
    {n : ℕ} {p : Poly σ} (h : HasExactDeterminant n p) :
    HasBorderDeterminant n p := by
  rcases h with ⟨hn, A₀, A, hp⟩
  refine ⟨hn, (fun _ => A₀), (fun _ => A), ?_⟩
  intro d
  simpa only [hp] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => p.coeff d) atTop (𝓝 (p.coeff d)))

end PermanentBorder

end OAI
end

section
-- module Solutions.OAIQW_PermanentBorder.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PermanentBorder
open MvPolynomial

theorem permanent_exact_cubic_lower_bound_oai (m n : ℕ) (hm : 1408 ≤ m)
    (h : HasExactDeterminant n (permanentPolynomial m)) :
    (m : ℝ)^3 / (5529600 * Real.exp 1) ≤ (n : ℝ) :=
  permanent_border_cubic_lower_bound m n hm h.hasBorderDeterminant

end PermanentBorder

end OAI
end

theorem solution : type_of% @OAI.PermanentBorder.permanent_exact_cubic_lower_bound_oai := @OAI.PermanentBorder.permanent_exact_cubic_lower_bound_oai
