-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator.arbitraryRowAxialRaise_sameAxis_diamond_iff_commutator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/7b82ce41-6ddb-422d-bcab-0f83558d7765

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondGapShift_arbitraryRowAxialRaise_raiseWeight_later
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_ArbitraryRowSameAxisDiamondPathCommutator_arbitraryRowAxialRaise_raiseWeight_eq_sub_omitted

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
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowFirstAxisIntertwining
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapShift
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (i j : Fin (r + 1)) (hij : i < j)
    (hdom : lam j ≤ lam i) (k : Fin n) :
    ((arbitraryRowAxialRaise (raiseWeight lam i) j k).comp
        (arbitraryRowAxialRaise lam i k) =
      (arbitraryRowAxialRaise (raiseWeight lam j) i k).comp
        (arbitraryRowAxialRaise lam j k)) ↔
      ((arbitraryRowAxialRaise lam j k).comp
          (arbitraryRowAxialRaise lam i k) -
        (arbitraryRowAxialRaise lam i k).comp
          (arbitraryRowAxialRaise lam j k) =
          (diamondOmittedRowOperator lam j i k).comp
            (arbitraryRowAxialRaise lam i k)) := by
  rw [arbitraryRowAxialRaise_raiseWeight_eq_sub_omitted
    lam j i hij hdom k,
    arbitraryRowAxialRaise_raiseWeight_later lam i j hij k,
    LinearMap.sub_comp]
  constructor
  · intro h
    have h' := (sub_eq_iff_eq_add).mp h
    rw [h']
    abel
  · intro h
    have h' := (sub_eq_iff_eq_add).mp h
    rw [h']
    abel
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
