-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension.fullBranchSignature_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.063146+00:00
-- url     : https://prove2.me/submissions/eb0acfc7-c6bb-40f7-a512-3c29448f22dc

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
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherYoungGraphAssembly
open MetricCodes.Spherical.MixedTensorRepresentations
namespace MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
theorem _root_.solution {r : ℕ}
    {lam : Fin (r + 1) → ℕ}
    (mu : FullBranchWeight lam) : Antitone (fullBranchSignature mu) := by
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact (fullBranchSignature_le mu i.succ).trans
    (fullBranchSignature_succ_le mu i)
end MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
