-- Prove2me | solution 1 for MetricCodes.Johnson.Rate.binaryRate_le_combinedVariationalRate_of_projectionGrams
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/36eeafa2-1be5-4719-8177-d4ae6fff6e86

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_binaryRate_le_variationalRate
import Theorems.Thm_MetricCodes_Johnson_Rate_binaryRate_le_variationalRate_of_projectionGrams

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
    MetricCodes.Hamming.binaryRate d ≤
      MetricCodes.Johnson.combinedVariationalRate d := by
  unfold MetricCodes.Johnson.combinedVariationalRate
  exact le_min
    (MetricCodes.Hamming.binaryRate_le_variationalRate hd hdhalf)
    (binaryRate_le_variationalRate_of_projectionGrams hd hdhalf hdata)
end MetricCodes.Johnson.Rate
