-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.compactified_certificate_residual_threshold_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/c7ed3ab9-ae97-45b7-a249-cce2f730824a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_certificate_threshold_le

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
    {r j : ℕ} {u : ℕ → ℝ}
    {a : ℕ → Fin (r + 1) → ℝ}
    {b : ℕ → Fin r → ℝ}
    {A : Fin (j + 1) → ℝ} {B : Fin j → ℝ}
    {φ : ℕ → ℕ} {s c : ℝ}
    (hφ : StrictMono φ)
    (hthreshold : Tendsto u atTop (nhds s))
    (hfeasible : ∀ n, u n < 2 * Gamma (a n) (b n))
    (hspectral : Tendsto
      (fun n => Gamma (a (φ n)) (b (φ n)))
      atTop (nhds (((1 - c ^ 2) / 2) + c ^ 2 * Gamma A B))) :
    s ≤ 1 - c ^ 2 * (1 - 2 * Gamma A B) := by
  have h := compactified_certificate_threshold_le
    hφ hthreshold hfeasible hspectral
  nlinarith
end MetricCodes.Spherical.HigherHierarchy
