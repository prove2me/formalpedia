-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath.spectralPathCoeff_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.858473+00:00
-- url     : https://prove2.me/submissions/554f6426-d996-4313-a41d-75f392b47425

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
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonLastRoot
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondGapDifference
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
theorem _root_.solution {r : ℕ}
    (lam : Fin (r + 1) → ℕ)
    (pivot a : Fin (r + 1)) (t : ℝ)
    (S : Finset (Fin (r + 1)))
    (ha : a < pivot) (haS : a ∉ S) :
    spectralPathCoeff lam pivot t S =
      -(shiftedRowGap lam pivot a + t) *
        spectralPathCoeff lam pivot t (insert a S) := by
  classical
  have hamem : a ∈ precedingRows pivot \ S := by
    simp [ha, haS]
  have hprod := Finset.mul_prod_erase
    (precedingRows pivot \ S)
      (fun b => shiftedRowGap lam pivot b + t) hamem
  have hdiff : precedingRows pivot \ insert a S =
      (precedingRows pivot \ S).erase a :=
    Finset.sdiff_insert (precedingRows pivot) S a
  unfold spectralPathCoeff
  rw [Finset.card_insert_of_notMem haS, hdiff, pow_succ, ← hprod]
  ring
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
