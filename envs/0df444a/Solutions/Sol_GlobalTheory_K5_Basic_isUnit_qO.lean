-- Prove2me | solution 1 for GlobalTheory.K5.Basic.isUnit_qO
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:24:50.191678+00:00
-- url     : https://prove2.me/submissions/52e1a46f-0039-4135-a397-fbf79aa5158f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotCoboundaryConstantOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.K5 GlobalTheory.K5.Basic
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]
namespace GlobalTheory.K5.Basic
theorem _root_.solution : IsUnit (qO p) := by
  refine IsUnit.map _ (IsUnit.of_mul_eq_one (HahnSeries.single (-1 : ℤ) (1 : ℤ_[p])) ?_)
  rw [HahnSeries.single_mul_single]; simp [HahnSeries.single_zero_one]
end GlobalTheory.K5.Basic
