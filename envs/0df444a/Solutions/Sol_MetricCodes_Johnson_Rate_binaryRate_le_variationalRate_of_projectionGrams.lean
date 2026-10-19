-- Prove2me | solution 1 for MetricCodes.Johnson.Rate.binaryRate_le_variationalRate_of_projectionGrams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/f57532bd-4acb-4243-8c16-3c8f9fb2f09b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_rateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Johnson_Rate_rateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Johnson_Rate_binaryRate_le_shellRate_of_projectionGrams

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Rate
open MetricCodes.Johnson.Asymptotics
open MetricCodes.Johnson.SpectralAsymptotics
namespace MetricCodes.Johnson.Rate
theorem _root_.solution
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2)
    (hdata : ∀ a b g u : ℝ,
      MetricCodes.Johnson.Feasible d a b g u →
        ∀ᶠ n : ℕ in atTop,
          Nonempty
            (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤ MetricCodes.Johnson.variationalRate d := by
  apply le_csInf (rateSet_nonempty_of_interior hd hdhalf)
  rintro r ⟨a, b, g, u, hfeasible, rfl⟩
  exact binaryRate_le_shellRate_of_projectionGrams
    hfeasible (hdata a b g u hfeasible)
end MetricCodes.Johnson.Rate
