-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator.polarization_arbitraryRowAxialRaise_commutator_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/96bc620c-e6b2-4cbf-9b01-68fc3205a781

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondRootCommutator_polarization_axialCoordinate_mul_lowerPolarizationPath_sub

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
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (row a b : Fin (r + 1)) (k : Fin n)
    (p : PolynomialSpace r n) :
    polarization r n a b (arbitraryRowAxialRaise lam row k p) -
        arbitraryRowAxialRaise lam row k (polarization r n a b p) =
      ∑ S ∈ (precedingRows row).powerset,
        polarizationPathCoefficient lam row S •
          ((if b = polarizationPathStart row S then
            MvPolynomial.X (variableIndex a k) *
              lowerPolarizationPath
                ((S.sort (· ≤ ·)) ++ [row]) p
          else 0) +
            MvPolynomial.X
                (variableIndex (polarizationPathStart row S) k) *
              upperPolarizationPathCommutator a b
                ((S.sort (· ≤ ·)) ++ [row]) p) := by
  classical
  rw [arbitraryRowAxialRaise_apply, map_sum,
    arbitraryRowAxialRaise_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  rw [map_smul, ← smul_sub,
    polarization_axialCoordinate_mul_lowerPolarizationPath_sub]
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
