-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition.diamondPairResidual_eq_prefix_comp_suffix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/b8c32bab-b5d3-4346-aa6e-b8fd613dd698

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondSuffixRootCommute_lowerPolarizationPath_arbitraryRowAxialRaise_commute_of_gt
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondResidualSuffixPartition_diamondPathOperator_eq_omittedPrefix_comp_suffix
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondResidualSuffixPartition_diamondPathOperator_eq_insertedPrefix_comp_suffix

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
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixRootCommute
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot : Fin (r + 1)) (hpivot : pivot < target) (k : Fin n)
    (S : Finset (Fin (r + 1)))
    (front : List (Fin (r + 1)))
    (next : Fin (r + 1)) (tail : List (Fin (r + 1)))
    (homit : (S.sort (· ≤ ·)) ++ [target] = front ++ next :: tail)
    (hinsert : ((insert pivot S).sort (· ≤ ·)) ++ [target] =
      front ++ pivot :: next :: tail)
    (hnext : pivot < next)
    (htail : ∀ a ∈ tail, pivot < a) :
    diamondPairResidual lam target pivot k S =
      (diamondPrefixResidual lam target pivot k S front next).comp
        (lowerPolarizationPath (next :: tail)) := by
  let suffix : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
    lowerPolarizationPath (next :: tail)
  let Z : PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n :=
    arbitraryRowAxialRaise lam pivot k
  have hcomm : suffix.comp Z = Z.comp suffix := by
    apply LinearMap.ext
    intro p
    exact lowerPolarizationPath_arbitraryRowAxialRaise_commute_of_gt
      lam pivot k (next :: tail)
      (by
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hnext
        · exact htail a ha)
      p
  rw [diamondPairResidual,
    diamondPathOperator_eq_omittedPrefix_comp_suffix
      target pivot k S front next tail homit,
    diamondPathOperator_eq_insertedPrefix_comp_suffix
      target pivot k S front next tail hinsert]
  change
    ((((insertedDiamondPrefix target pivot k S front next).comp suffix).comp Z -
      Z.comp ((insertedDiamondPrefix target pivot k S front next).comp suffix)) -
      shiftedRowGap lam target pivot •
        (((omittedDiamondPrefix target k S front next).comp suffix).comp Z -
          Z.comp ((omittedDiamondPrefix target k S front next).comp suffix))) -
        ((omittedDiamondPrefix target k S front next).comp suffix).comp Z =
      (diamondPrefixResidual lam target pivot k S front next).comp suffix
  simp only [diamondPrefixResidual, LinearMap.sub_comp,
    LinearMap.smul_comp, LinearMap.comp_assoc, hcomm]
  rfl
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
