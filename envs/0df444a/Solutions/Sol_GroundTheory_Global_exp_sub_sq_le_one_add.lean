-- Prove2me | solution 1 for GroundTheory.Global.exp_sub_sq_le_one_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:08:40.079701+00:00
-- url     : https://prove2.me/submissions/6961e58b-c309-40c0-9165-0a01eb0720f8

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
theorem _root_.solution {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) :
    Real.exp (x - x ^ 2) ≤ 1 + x := by
  have hy0 : 0 ≤ x - x ^ 2 := by nlinarith
  have hy1 : x - x ^ 2 ≤ x := by nlinarith
  have h := Real.abs_exp_sub_one_sub_id_le (x := x - x ^ 2) (by rw [abs_le]; constructor <;> linarith)
  have h' := (abs_le.mp h).2
  nlinarith [mul_le_mul hy1 hy1 hy0 hx0]
end GroundTheory.Global
