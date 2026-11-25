-- Prove2me | solution 1 for GroundTheory.Global.le_exp_sub_one_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:28:00.080846+00:00
-- url     : https://prove2.me/submissions/cc91d973-5b6a-49b7-a65d-8747598aae15

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
namespace GroundTheory.Global
theorem _root_.solution {y : ℤᵐ⁰} {n : ℤ} (h : y < exp n) : y ≤ exp (n - 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_le
  rw [← log_le_iff_le_exp hy]
  have := (log_lt_iff_lt_exp hy).2 h
  omega
end GroundTheory.Global
