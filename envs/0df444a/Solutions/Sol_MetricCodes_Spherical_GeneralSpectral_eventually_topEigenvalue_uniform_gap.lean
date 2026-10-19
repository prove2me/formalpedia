-- Prove2me | solution 1 for MetricCodes.Spherical.GeneralSpectral.eventually_topEigenvalue_uniform_gap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.020426+00:00
-- url     : https://prove2.me/submissions/b78579f8-ed14-442c-b0ab-b499e76c6fca

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_topEigenvalue_gt
import Theorems.Thm_MetricCodes_Johnson_SpectralAsymptotics_eventually_topEigenvalue_gt
import Theorems.Thm_MetricCodes_Spherical_GeneralSpectral_eventually_topEigenvalue_gt

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
theorem _root_.solution {a b s : ℝ}
    (hb : 0 ≤ b) (hba : b < a)
    (hs : s < 2 * MetricCodes.Gamma a b) :
    ∀ᶠ n : ℕ in atTop,
      s + spectralGap s a b <
        SpherePacking.Jacobi.topEigenvalue
          n (transverseDegree b n) (longitudinalDegree a n) := by
  apply eventually_topEigenvalue_gt hb hba
  unfold spectralGap
  linarith
end MetricCodes.Spherical.GeneralSpectral
