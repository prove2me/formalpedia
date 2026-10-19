-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.tendsto_terminal_degree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/b7cd1715-31f6-4c1c-aec7-b973110d3b78

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_longitudinal_ratio
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_longitudinal_ratio
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_tendsto_longitudinalDegree_atTop

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped BigOperators Nat Topology InnerProductSpace
open MetricCodes.Spherical.GeneralSpectral
namespace MetricCodes.Spherical.GeneralSpectral
theorem _root_.solution {a : ℝ}
    (ha : 0 < a) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  have hoffset :
      Tendsto (fun n : ℕ => (r : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have hmain := (tendsto_longitudinal_ratio ha.le).sub hoffset
  rw [sub_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards [
    (tendsto_longitudinalDegree_atTop ha).eventually
      (eventually_ge_atTop r)] with n hn
  rw [Nat.cast_sub hn]
  ring
end MetricCodes.Spherical.GeneralSpectral
