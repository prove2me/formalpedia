-- Prove2me | solution 1 for MetricCodes.Johnson.Asymptotics.tendsto_complementDegree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.299848+00:00
-- url     : https://prove2.me/submissions/add343c9-74d1-4bce-a4ed-94ec0df9c285

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_longitudinal_ratio

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Johnson
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics
namespace MetricCodes.Johnson.Asymptotics
theorem _root_.solution {g : ℝ} (hg : 0 ≤ g) :
    Tendsto (fun n : ℕ => (complementDegree g n : ℝ) / (n : ℝ))
      atTop (nhds g) := by
  simpa [complementDegree] using
    MetricCodes.Hamming.tendsto_longitudinal_ratio hg
end MetricCodes.Johnson.Asymptotics
