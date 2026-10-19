-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining.sum_powerset_erase_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/63487a89-5538-4140-bb69-791b34cea66b

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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.GelfandTsetlin
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
theorem _root_.solution
    {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (P : Finset α) (a : α) (ha : a ∈ P) (f : Finset α → M) :
    (∑ S ∈ P.powerset, f S) =
      ∑ S ∈ (P.erase a).powerset, (f S + f (insert a S)) := by
  classical
  calc
    (∑ S ∈ P.powerset, f S) =
        ∑ S ∈ (insert a (P.erase a)).powerset, f S := by
          rw [Finset.insert_erase ha]
    _ = (∑ S ∈ (P.erase a).powerset, f S) +
          ∑ S ∈ (P.erase a).powerset, f (insert a S) := by
          rw [Finset.sum_powerset_insert (by simp)]
    _ = ∑ S ∈ (P.erase a).powerset,
          (f S + f (insert a S)) := by
          rw [Finset.sum_add_distrib]
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
