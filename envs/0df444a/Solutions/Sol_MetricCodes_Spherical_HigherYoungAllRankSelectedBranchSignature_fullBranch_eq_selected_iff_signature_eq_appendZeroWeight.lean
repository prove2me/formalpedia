-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature.fullBranch_eq_selected_iff_signature_eq_appendZeroWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/19627ed8-f97b-4290-a40c-c8f64afd9dfd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRankBranching_fullBranchOfInterlaces_signature_eq_appendZeroWeight

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
    nu = fullBranchOfInterlaces mu h ↔
      fullBranchSignature nu = appendZeroWeight mu := by
  constructor
  · intro hnu
    rw [hnu, fullBranchOfInterlaces_signature_eq_appendZeroWeight]
  · intro hnu
    apply Subtype.ext
    funext i
    apply Fin.ext
    change fullBranchSignature nu i =
      fullBranchSignature (fullBranchOfInterlaces mu h) i
    rw [fullBranchOfInterlaces_signature_eq_appendZeroWeight]
    exact congrFun hnu i
end MetricCodes.Spherical.HigherYoungAllRankSelectedBranchSignature
