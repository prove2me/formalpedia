-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator.polarization_axialCoordinate_mul_lowerPolarizationPath_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/102bb3ed-c39f-42f3-b218-67fd2df9ccba

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankLowerRowBranching
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
theorem _root_.solution
    {r n : ℕ} (a b start : Fin (r + 1)) (k : Fin n)
    (path : List (Fin (r + 1))) (p : PolynomialSpace r n) :
    polarization r n a b
        (MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath path p) -
        MvPolynomial.X (variableIndex start k) *
          lowerPolarizationPath path (polarization r n a b p) =
      (if b = start then
        MvPolynomial.X (variableIndex a k) *
          lowerPolarizationPath path p
      else 0) +
        MvPolynomial.X (variableIndex start k) *
          upperPolarizationPathCommutator a b path p := by
  rw [polarization_mul_euler, polarization_X_euler,
    polarization_lowerPolarizationPath_commutator]
  split_ifs <;> ring
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
