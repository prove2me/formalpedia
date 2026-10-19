-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal.iteratedArbitraryRowAxialRaise_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/7408e3b2-9a51-4013-a80c-d6349b6107de

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherYoungMixedGapBranching
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ) (k : Fin n)
    (rows rows' : List (Fin (r + 1))) :
    iteratedArbitraryRowAxialRaise lam k (rows ++ rows') =
      (iteratedArbitraryRowAxialRaise
        (arbitraryRowPathWeight lam rows) k rows').comp
        (iteratedArbitraryRowAxialRaise lam k rows) := by
  induction rows generalizing lam with
  | nil => simp [iteratedArbitraryRowAxialRaise, arbitraryRowPathWeight]
  | cons row rows ih =>
      simp only [List.cons_append, iteratedArbitraryRowAxialRaise,
        arbitraryRowPathWeight]
      rw [ih (raiseWeight lam row)]
      exact LinearMap.comp_assoc _ _ _
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonGramIdeal
