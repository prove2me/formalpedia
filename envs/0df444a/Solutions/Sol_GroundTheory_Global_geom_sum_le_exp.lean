-- Prove2me | solution 1 for GroundTheory.Global.geom_sum_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:09:55.218262+00:00
-- url     : https://prove2.me/submissions/50085c5e-3f57-4d29-a1c4-63de422a54aa

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (M : ℕ) :
    ∑ k ∈ Finset.range M, x ^ k ≤ Real.exp (x + 2 * x ^ 2) := by
  have h1 : ∑ k ∈ Finset.range M, x ^ k ≤ 1 / (1 - x) := by
    rw [Finset.range_eq_Ico]
    calc ∑ k ∈ Finset.Ico 0 M, x ^ k ≤ x ^ 0 / (1 - x) :=
          geom_sum_Ico_le_of_lt_one hx0 (by linarith)
      _ = 1 / (1 - x) := by rw [pow_zero]
  have h2 : 1 / (1 - x) ≤ 1 + x + 2 * x ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (sq_nonneg x) (by linarith : (0 : ℝ) ≤ 1 - 2 * x)]
  have h3 := Real.add_one_le_exp (x + 2 * x ^ 2)
  linarith
end GroundTheory.Global
