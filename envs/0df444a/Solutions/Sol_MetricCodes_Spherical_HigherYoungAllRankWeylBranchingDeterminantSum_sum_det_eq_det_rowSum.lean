-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum.sum_det_eq_det_rowSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/b5ec8676-9163-4809-97d8-4fc72656b7f6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankWeylBranchingDeterminantSum_det_rowSum_eq_sum_det

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
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
namespace MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {R : Type*} [CommRing R]
    {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (row : ∀ i, κ i → ι → R) :
    (∑ a : (∀ i, κ i),
        Matrix.det (fun i j => row i (a i) j)) =
      Matrix.det (fun i j => ∑ a : κ i, row i a j) :=
  (det_rowSum_eq_sum_det row).symm
end MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
