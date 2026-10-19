-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching.appendZeroWeight_eq_snoc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/5291ad6f-828d-4c2e-bc6a-7cf3d88512f0

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherHarmonicYoung.DeterminantVectors
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
theorem _root_.solution {r : ℕ}
    (mu : Fin (r + 1) → ℕ) :
    appendZeroWeight mu = Fin.snoc mu 0 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [appendZeroWeight]
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
