-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactified_certificate_entropy_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/51ec4db5-dabd-4248-8868-c3867c904f7b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_certificate_slack_of_strictMono

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {a : ℕ → Fin (r + 1) → ℝ}
    {b : ℕ → Fin r → ℝ} {φ : ℕ → ℕ} {R L : ℝ}
    (hφ : StrictMono φ)
    (hbound : ∀ n, Phi (a n) (b n) ≤
      R + 1 / ((n : ℝ) + 1))
    (hlimit : Tendsto (fun n => Phi (a (φ n)) (b (φ n)))
      atTop (nhds L)) :
    L ≤ R := by
  have hupper : Tendsto
      (fun n : ℕ => R + 1 / ((φ n : ℝ) + 1))
      atTop (nhds R) := by
    simpa using (tendsto_const_nhds (x := R)).add
      (tendsto_certificate_slack_of_strictMono hφ)
  exact le_of_tendsto_of_tendsto hlimit hupper
    (Filter.Eventually.of_forall fun n => hbound (φ n))
end MetricCodes.Spherical.HigherHierarchy
