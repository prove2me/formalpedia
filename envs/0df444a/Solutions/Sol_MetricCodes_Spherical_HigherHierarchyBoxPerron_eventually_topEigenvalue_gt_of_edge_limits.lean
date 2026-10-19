-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.eventually_topEigenvalue_gt_of_edge_limits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/654765f5-2ef6-4668-bd55-9cbc98087a28

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_constantRayleigh_tendsto
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_constantRayleigh_le_top

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
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxPerron
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
namespace MetricCodes.Spherical.HigherHierarchyBoxPerron
theorem _root_.solution {r m : ℕ}
    (edge : ℕ → BoxVertex r m → Fin (r + 1) → ℝ)
    (weight : Fin (r + 1) → ℝ)
    (hlimit : ∀ (v : BoxVertex r m) (i : Fin (r + 1)),
      Tendsto (fun n : ℕ => edge n v i) atTop (nhds (weight i)))
    {s : ℝ}
    (hspectral :
      s < (2 * (m : ℝ) / (m + 1 : ℝ)) *
        ∑ i : Fin (r + 1), weight i) :
    ∀ᶠ n : ℕ in atTop,
      s < HigherHierarchyFinitePerron.topEigenvalue
        (adjacencyMatrix (edge n)) := by
  have h := (constantRayleigh_tendsto edge weight hlimit).eventually
    (Ioi_mem_nhds hspectral)
  filter_upwards [h] with n hn
  exact hn.trans_le (constantRayleigh_le_top (edge n))
end MetricCodes.Spherical.HigherHierarchyBoxPerron
