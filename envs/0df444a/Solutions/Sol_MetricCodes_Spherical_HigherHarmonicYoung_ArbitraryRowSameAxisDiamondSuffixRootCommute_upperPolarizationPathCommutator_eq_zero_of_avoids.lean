-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute.upperPolarizationPathCommutator_eq_zero_of_avoids
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/3ec20b04-1a2c-4e16-a094-f8ddbe50cce7

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
    {r n : ℕ} (a b : Fin (r + 1))
    (path : List (Fin (r + 1)))
    (ha : a ∉ path) (hb : b ∉ path) :
    upperPolarizationPathCommutator (n := n) a b path = 0 := by
  induction path with
  | nil => rfl
  | cons i rest ih =>
      cases rest with
      | nil => rfl
      | cons j tail =>
          have harest : a ∉ j :: tail := by
            intro h
            exact ha (by simp [h])
          have hbrest : b ∉ j :: tail := by
            intro h
            exact hb (by simp [h])
          have hbjne : b ≠ j := by
            intro h
            subst b
            exact hb (by simp)
          have hiane : i ≠ a := by
            intro h
            subst i
            exact ha (by simp)
          change
            (polarization r n j i).comp
                (upperPolarizationPathCommutator a b (j :: tail)) +
              (if b = j then
                (polarization r n a i).comp
                  (lowerPolarizationPath (j :: tail))
              else 0) -
              (if i = a then
                (polarization r n j b).comp
                  (lowerPolarizationPath (j :: tail))
              else 0) = 0
          rw [ih harest hbrest, if_neg hbjne, if_neg hiane]
          simp
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
