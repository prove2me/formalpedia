-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute.lowerPolarizationPath_arbitraryRowAxialRaise_commute_of_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/8e73f90b-7b22-4d36-abba-a51436c6812f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixRootCommute_polarization_arbitraryRowAxialRaise_commute_of_gt

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
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row : Fin (r + 1)) (k : Fin n)
    (path : List (Fin (r + 1)))
    (hpath : ∀ q ∈ path, row < q)
    (p : PolynomialSpace r n) :
    lowerPolarizationPath path (arbitraryRowAxialRaise lam row k p) =
      arbitraryRowAxialRaise lam row k (lowerPolarizationPath path p) := by
  induction path generalizing p with
  | nil => rfl
  | cons first rest ih =>
      cases rest with
      | nil => rfl
      | cons next tail =>
          have hfirst : row < first := hpath first (by simp)
          have hnext : row < next := hpath next (by simp)
          have hrest : ∀ q ∈ (next :: tail), row < q := by
            intro q hq
            exact hpath q (by simp [hq])
          change
            polarization r n next first
                (lowerPolarizationPath (next :: tail)
                  (arbitraryRowAxialRaise lam row k p)) =
              arbitraryRowAxialRaise lam row k
                (polarization r n next first
                  (lowerPolarizationPath (next :: tail) p))
          rw [ih hrest]
          exact polarization_arbitraryRowAxialRaise_commute_of_gt
            lam row next first hnext hfirst k _
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
