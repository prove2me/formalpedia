-- Prove2me | solution 1 for MetricCodes.Johnson.eventually_projectionGram
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/86e0313c-8632-4b0d-a9f5-29b3008a5743

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_admissibleDegrees
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_eventually_terminal_block_fit
import Theorems.Thm_MetricCodes_Johnson_Rate_eventually_strict_weight_half

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson
theorem _root_.solution
    {d a b g u : ℝ}
    (h : Feasible d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty
        (ProjectionGram n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n)) := by
  filter_upwards [eventually_admissibleDegrees h.1,
    MetricCodes.Johnson.Rate.eventually_strict_weight_half h.1,
    MetricCodes.Johnson.SpectralAsymptotics.eventually_terminal_block_fit h.1 0]
    with n hadmissible hstrict hfit
  refine ⟨johnsonProjectionGram hadmissible hstrict ?_⟩
  omega
end MetricCodes.Johnson
