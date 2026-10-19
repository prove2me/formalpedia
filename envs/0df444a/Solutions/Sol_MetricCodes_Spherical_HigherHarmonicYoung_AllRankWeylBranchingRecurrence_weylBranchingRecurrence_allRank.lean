-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence.weylBranchingRecurrence_allRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/be0aec91-ae85-42ae-a629-0900753deb90

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankWeylBranchingRecurrence_orthogonalJacobiTrudiDimension_branching_allRank
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankWeylBranchingRecurrence_weylBranchingRecurrence_of_jacobiTrudi_branching

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
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingDeterminantSum
open MetricCodes.Spherical.HigherYoungAllRankWeylBranchingRowDifference
open MetricCodes.Spherical.HigherYoungOrthogonalBranchCompleteCoefficient
open MetricCodes.Spherical.HigherWeylAllRankJacobiTrudiWeylEvaluation
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherHierarchy
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
theorem _root_.solution
    {r n : ℕ} (hn : 2 * r + 5 ≤ n)
    (lam : Fin (r + 1) → ℕ) (hdom : Antitone lam) :
    WeylBranchingRecurrence n lam :=
  weylBranchingRecurrence_of_jacobiTrudi_branching hn lam
    (orthogonalJacobiTrudiDimension_branching_allRank (by omega) lam hdom)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankWeylBranchingRecurrence
