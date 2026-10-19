-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.tendsto_complementWeight_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:31.72047+00:00
-- url     : https://prove2.me/submissions/8ab7bad6-67c6-4dfd-8392-abb6ffd92100

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_complement_longitudinal_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
open MetricCodes.Johnson.SpectralAsymptotics
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.SpectralAsymptotics
theorem _root_.solution
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        ((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  simpa [shellWeight] using
    MetricCodes.Hamming.tendsto_complement_longitudinal_ratio ha ha'
end MetricCodes.Johnson.SpectralAsymptotics
