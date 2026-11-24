-- Prove2me | solution 1 for GlobalTheory.LGrowth.measurable_summatory
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:18.918294+00:00
-- url     : https://prove2.me/submissions/2bc0bdfc-56f7-4c6a-8dab-ab1df49d4d56

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
theorem _root_.solution (f : ℕ → ℂ) : Measurable (summatory f) :=
  (measurable_from_top (f := fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, f k)).comp Nat.measurable_floor
end GlobalTheory.LGrowth
