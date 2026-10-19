-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance.ambientCoordinateDerivation_zeroRowPolynomial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/61abf16f-bd8d-4e49-be2e-9e6660b0c2bd

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
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.ThreeRowYoungBranching
namespace MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
theorem _root_.solution
    {r n : ℕ} (a b : Fin n) (p : PolynomialSpace r n) :
    ambientCoordinateDerivation (r := r + 1) a b
        (zeroRowPolynomial n p) =
      zeroRowPolynomial n
        (ambientCoordinateDerivation (r := r) a b p) := by
  rw [ambientCoordinateDerivation_apply, Fin.sum_univ_castSucc]
  simp only [pderiv_zeroRowPolynomial_castSucc,
    pderiv_zeroRowPolynomial_lastRow, mul_zero, add_zero]
  rw [ambientCoordinateDerivation_apply, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, zeroRowPolynomial_X]
end MetricCodes.Spherical.HigherYoungAllRankZeroRowRotationEquivariance
