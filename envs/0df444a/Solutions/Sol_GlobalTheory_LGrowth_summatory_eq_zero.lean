-- Prove2me | solution 1 for GlobalTheory.LGrowth.summatory_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:38.238746+00:00
-- url     : https://prove2.me/submissions/d44396db-31e0-432b-b56b-19c5a00ea50c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableAtMellinSummatory

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.LGrowth
open Filter Topology Asymptotics
variable {f : ℕ → ℂ} {C : ℝ}
namespace GlobalTheory.LGrowth
theorem _root_.solution {t : ℝ} (ht : t < 1) : summatory f t = 0 := by
  simp [summatory, Nat.floor_eq_zero.2 ht]
end GlobalTheory.LGrowth
