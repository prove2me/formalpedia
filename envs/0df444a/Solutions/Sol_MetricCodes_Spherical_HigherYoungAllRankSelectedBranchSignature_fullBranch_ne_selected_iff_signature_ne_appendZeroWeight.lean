-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature.fullBranch_ne_selected_iff_signature_ne_appendZeroWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/8fb905e8-fa5c-4466-9e39-f433dc1c2e84

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankSelectedBranchSignature_fullBranch_eq_selected_iff_signature_eq_appendZeroWeight

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
open MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
theorem _root_.solution
    {r : ℕ} {lam : Fin (r + 2) → ℕ}
    (mu : Fin (r + 1) → ℕ) (h : Interlaces lam mu)
    (nu : FullBranchWeight lam) :
    nu ≠ fullBranchOfInterlaces mu h ↔
      fullBranchSignature nu ≠ appendZeroWeight mu := by
  exact not_congr
    (fullBranch_eq_selected_iff_signature_eq_appendZeroWeight mu h nu)
end MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
