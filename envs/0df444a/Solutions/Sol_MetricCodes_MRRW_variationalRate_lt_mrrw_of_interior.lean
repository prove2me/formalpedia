-- Prove2me | solution 1 for MetricCodes.MRRW.variationalRate_lt_mrrw_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/56db68ab-91e7-4817-9cdb-9c815777a012

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Johnson_variationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_MRRW_exists_zero_fibre_boundary_of_interior_minimizer
import Theorems.Thm_MetricCodes_MRRW_interior_shell_improvement

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hstrict :
      MetricCodes.Johnson.mrrwRate δ < MetricCodes.Hamming.classicalRate δ) :
    MetricCodes.Johnson.variationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by
  obtain ⟨a, u, hu, hua, ha, _hweight, hboundary, hrate⟩ :=
    exists_zero_fibre_boundary_of_interior_minimizer
      hδ hhalf hstrict
  obtain ⟨A, b, g, _hb, _hg, hfeasible, himprovement⟩ :=
    interior_shell_improvement hδ hhalf hu hua ha hboundary
  calc
    MetricCodes.Johnson.variationalRate δ ≤
        MetricCodes.Johnson.shellRate A b g u :=
      MetricCodes.Johnson.variationalRate_le_of_feasible hfeasible
    _ < MetricCodes.Johnson.shellRate a 0 0 u := himprovement
    _ = MetricCodes.Johnson.mrrwRate δ := hrate.symm
end MetricCodes.MRRW
