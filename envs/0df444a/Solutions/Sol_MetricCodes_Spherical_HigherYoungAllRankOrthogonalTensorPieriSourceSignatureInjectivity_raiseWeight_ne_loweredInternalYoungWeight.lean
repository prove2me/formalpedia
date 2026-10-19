-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity.raiseWeight_ne_loweredInternalYoungWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/ed2c4d97-6bff-4c5d-8d1d-fef7a8dce8e5

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
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungPenultimateRowProjectedLower
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
theorem _root_.solution {r : ℕ}
    (lam : Fin (r + 1) → ℕ) (i j : Fin (r + 1)) :
    raiseWeight lam i ≠ loweredInternalYoungWeight lam j := by
  intro hij
  have hcoordinate := congrFun hij i
  by_cases heq : i = j
  · subst j
    simp [raiseWeight, loweredInternalYoungWeight] at hcoordinate
    omega
  · simp [raiseWeight, loweredInternalYoungWeight, heq] at hcoordinate
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalTensorPieriSourceSignatureInjectivity
