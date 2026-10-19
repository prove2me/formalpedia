-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.lagrangeWeight_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/bc649aad-f2a3-43e9-8079-f22fe6935421

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {c : ℝ} (hc : 0 < c)
    (i : Fin (r + 1)) :
    lagrangeWeight (scaleAmbient c a) (scaleStabilizer c b) i =
      lagrangeWeight a b i := by
  unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
    scaleAmbient scaleStabilizer
  rw [← Finset.prod_div_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [quadraticCoordinate_scaleCoordinate hc.le (h.ambient_nonneg i),
    quadraticCoordinate_scaleCoordinate hc.le (h.stabilizer_pos j).le,
    quadraticCoordinate_scaleCoordinate hc.le
      (h.ambient_nonneg (i.succAbove j))]
  field_simp [hc.ne']
end MetricCodes.Spherical.HigherHierarchy
