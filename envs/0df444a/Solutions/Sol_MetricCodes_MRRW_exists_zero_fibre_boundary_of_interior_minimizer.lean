-- Prove2me | solution 1 for MetricCodes.MRRW.exists_zero_fibre_boundary_of_interior_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/d4f94018-f9ba-4728-a9ac-998dfa4ce227

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Johnson_mrrwObjective_endpoint
import Theorems.Thm_MetricCodes_MRRW_exists_positive_mrrw_minimizer
import Theorems.Thm_MetricCodes_MRRW_inverse_zero_fibre_boundary

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
      MetricCodes.Johnson.mrrwRate δ <
        MetricCodes.Hamming.classicalRate δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwRate δ =
        MetricCodes.Johnson.shellRate a 0 0 u := by
  obtain ⟨r, hr, hupper, _hmin, hrate⟩ :=
    exists_positive_mrrw_minimizer hδ hhalf
  have hrstrict : r < 1 - 2 * δ := by
    rcases lt_or_eq_of_le hupper with hlt | heq
    · exact hlt
    · exfalso
      have hendpoint :
          MetricCodes.Johnson.mrrwRate δ =
            MetricCodes.Hamming.classicalRate δ := by
        calc
          MetricCodes.Johnson.mrrwRate δ =
              MetricCodes.Johnson.mrrwObjective δ r := hrate
          _ = MetricCodes.Johnson.mrrwObjective δ (1 - 2 * δ) := by
            rw [heq]
          _ = MetricCodes.Hamming.classicalRate δ :=
            MetricCodes.Johnson.mrrwObjective_endpoint hδ hhalf
      exact (ne_of_lt hstrict) hendpoint
  obtain ⟨a, u, hu, hua, ha, hweightdistance,
      hboundary, hobjective⟩ :=
    inverse_zero_fibre_boundary hδ hhalf hr hrstrict
  exact ⟨a, u, hu, hua, ha, hweightdistance,
    hboundary, hrate.trans hobjective⟩
end MetricCodes.MRRW
