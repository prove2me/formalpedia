-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector.gtRelativeCasimir_lower_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/557598fc-f659-4912-a8b9-2fc20b71a56c

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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 600000
open scoped BigOperators TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
theorem _root_.solution {r n : ℕ}
    (target source : Fin (r + 1) → ℕ) (row : Fin (r + 1))
    (hsource : target = raiseWeight source row) :
    (allRankCasimirEigenvalue n source -
      allRankCasimirEigenvalue n target - 1) / 2 =
      -ambientShift n target row := by
  subst target
  change
    (adjacentCasimirEigenvalue n source -
      adjacentCasimirEigenvalue n (raiseWeight source row) - 1) / 2 = _
  rw [adjacentCasimirEigenvalue_raiseWeight]
  unfold ambientShift raiseWeight
  simp only [Function.update_self, Nat.cast_add, Nat.cast_one]
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
