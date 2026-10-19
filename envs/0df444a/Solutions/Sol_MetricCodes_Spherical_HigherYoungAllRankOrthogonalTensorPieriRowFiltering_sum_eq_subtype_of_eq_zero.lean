-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering.sum_eq_subtype_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/01843c2b-6602-4328-983b-c8c70f306a60

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
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherWeylBinomialDeterminant
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriCoefficient
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriInvalidRows
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
theorem _root_.solution
    {ι A : Type*} [Fintype ι] [AddCommMonoid A]
    (P : ι → Prop) [DecidablePred P]
    (f : ι → A) (hzero : ∀ i : ι, ¬ P i → f i = 0) :
    (∑ i : ι, f i) = ∑ i : {i : ι // P i}, f i.val := by
  classical
  calc
    (∑ i : ι, f i) = ∑ i : ι, if P i then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P i
      · simp [hi]
      · simp [hi, hzero i hi]
    _ = ∑ i : {i : ι // P i}, f i.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype (Finset.univ.filter P) (by simp) f
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriRowFiltering
