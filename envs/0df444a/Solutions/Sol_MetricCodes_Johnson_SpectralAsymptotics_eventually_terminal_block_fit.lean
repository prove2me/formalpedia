-- Prove2me | solution 1 for MetricCodes.Johnson.SpectralAsymptotics.eventually_terminal_block_fit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/2a5abe4e-1e56-4afa-9b53-f1e92058b455

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_AsymptoticParameters_degree_pos
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_supportDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_complementDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_tendsto_terminalDegree_ratio
import Theorems.Thm_MetricCodes_Johnson_Asymptotics_eventually_degree_lt_of_ratio
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_tendsto_add_degree_add_fixed_ratio

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
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      supportDegree b n + complementDegree g n + r <
        terminalDegree u n := by
  have hfirst := tendsto_add_degree_add_fixed_ratio
    (tendsto_supportDegree_ratio h.support_nonneg)
    (tendsto_complementDegree_ratio h.complement_nonneg) r
  exact eventually_degree_lt_of_ratio hfirst
    (tendsto_terminalDegree_ratio h.degree_pos.le)
    h.first_lt_degree
end MetricCodes.Johnson.SpectralAsymptotics
