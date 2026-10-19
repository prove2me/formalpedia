-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactified_certificate_threshold_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/d3abb04d-0bf2-4c35-8880-72a44ce7a493

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
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {u : ℕ → ℝ}
    {a : ℕ → Fin (r + 1) → ℝ}
    {b : ℕ → Fin r → ℝ} {φ : ℕ → ℕ} {s Q : ℝ}
    (hφ : StrictMono φ)
    (hthreshold : Tendsto u atTop (nhds s))
    (hfeasible : ∀ n, u n < 2 * Gamma (a n) (b n))
    (hspectral : Tendsto
      (fun n => Gamma (a (φ n)) (b (φ n))) atTop (nhds Q)) :
    s ≤ 2 * Q := by
  have hu : Tendsto (fun n => u (φ n)) atTop (nhds s) :=
    hthreshold.comp hφ.tendsto_atTop
  have htwo : Tendsto
      (fun n => 2 * Gamma (a (φ n)) (b (φ n)))
      atTop (nhds (2 * Q)) :=
    hspectral.const_mul 2
  exact le_of_tendsto_of_tendsto hu htwo
    (Filter.Eventually.of_forall fun n => (hfeasible (φ n)).le)
end MetricCodes.Spherical.HigherHierarchy
