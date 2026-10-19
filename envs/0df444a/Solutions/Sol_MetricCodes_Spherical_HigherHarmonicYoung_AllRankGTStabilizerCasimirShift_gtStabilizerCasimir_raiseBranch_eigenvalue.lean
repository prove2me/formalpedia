-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift.gtStabilizerCasimir_raiseBranch_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:47.506255+00:00
-- url     : https://prove2.me/submissions/27f6deb7-d8c9-40bf-88f0-00746560dd16

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_raise_eigenvalue
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTStabilizerCasimirShift_stabilizerShift_succ_eq_ambientShift

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
set_option maxHeartbeats 2500000
open scoped BigOperators TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherYoungAllRankGTArrowheadSchurComplement
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
theorem _root_.solution {r n : ℕ}
    (mu : Fin (r + 1) → ℕ) (row : Fin (r + 1)) :
    (allRankCasimirEigenvalue n mu -
      allRankCasimirEigenvalue n (raiseWeight mu row)) / 2 =
      -stabilizerShift (n + 1) mu row - 1 / 2 := by
  have h := gtRelativeCasimir_raise_eigenvalue (n := n) mu row
  rw [← stabilizerShift_succ_eq_ambientShift] at h
  linarith
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTStabilizerCasimirShift
