-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator.arbitraryRowAxialRaise_commutator_sub_omitted_eq_sum_residual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/761126ef-8150-4b53-bc90-5c8d642c0dde

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondFullCommutator_arbitraryRowAxialRaise_eq_paired_paths

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathRecurrence
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target raised : Fin (r + 1)) (hrow : raised < target)
    (k : Fin n) :
    ((arbitraryRowAxialRaise lam target k).comp
          (arbitraryRowAxialRaise lam raised k) -
        (arbitraryRowAxialRaise lam raised k).comp
          (arbitraryRowAxialRaise lam target k)) -
        (diamondOmittedRowOperator lam target raised k).comp
          (arbitraryRowAxialRaise lam raised k) =
      ∑ S ∈ ((precedingRows target).erase raised).powerset,
        polarizationPathCoefficient lam target (insert raised S) •
          diamondPairResidual lam target raised k S := by
  classical
  apply LinearMap.ext
  intro p
  simp only [LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.sum_apply, LinearMap.smul_apply,
    diamondPairResidual_apply]
  rw [arbitraryRowAxialRaise_eq_paired_paths lam target raised hrow k
        (arbitraryRowAxialRaise lam raised k p),
      arbitraryRowAxialRaise_eq_paired_paths lam target raised hrow k p,
      diamondOmittedRowOperator_apply]
  simp_rw [map_sum, map_smul, map_sub]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro S _
  simp only [smul_sub, smul_smul, diamondPathOperator_apply, map_smul]
  module
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
