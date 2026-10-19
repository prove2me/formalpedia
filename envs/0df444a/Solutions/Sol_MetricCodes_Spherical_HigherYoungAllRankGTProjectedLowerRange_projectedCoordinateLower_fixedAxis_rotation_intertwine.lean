-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTProjectedLowerRange.projectedCoordinateLower_fixedAxis_rotation_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/0957969c-9b4b-4c36-be1a-58895c005716

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankGTProjectedLowerRange_euclideanAmbientRotation_castSucc_last

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
set_option maxHeartbeats 1200000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankGTProjectedLowerRange
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankGelfandTsetlinHarmonicIsometry
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankHarmonicBranchRotationIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ClebschRotation
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungCyclicHighestSchur
open MetricCodes.Spherical.HigherYoungMixedGapLieGram
open MetricCodes.Spherical.HigherYoungTwoRowLieIrreducibility
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherYoungAllRankGTProjectedLowerRange
theorem _root_.solution
    {r n : ℕ} (low high : Fin (r + 2) → ℕ)
    (hdeg : (∑ i, high i) = (∑ i, low i) + 1)
    (row : Fin (r + 2)) (a b : Fin n) :
    (projectedCoordinateLower low high hdeg row
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))).comp
        (youngAmbientRotation high a.castSucc b.castSucc) =
      (youngAmbientRotation low a.castSucc b.castSucc).comp
        (projectedCoordinateLower low high hdeg row
          (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n))) := by
  apply LinearMap.ext
  intro p
  have h := projectedCoordinateLower_rotation low high hdeg row
    a.castSucc b.castSucc
    (EuclideanSpace.basisFun (Fin (n + 1)) ℝ (Fin.last n)) p
  rw [euclideanAmbientRotation_castSucc_last] at h
  have hzero : projectedCoordinateLower low high hdeg row 0 p = 0 :=
    map_zero (projectedCoordinateLowerAxis low high hdeg row p)
  rw [hzero, zero_add] at h
  exact h.symm
end MetricCodes.Spherical.HigherYoungAllRankGTProjectedLowerRange
