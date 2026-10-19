-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation.sum_spectralLocalDiamondResidual_eq_spectralPrefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:43.40114+00:00
-- url     : https://prove2.me/submissions/22cf58ee-d3d1-4545-a4fc-dd6b91978ade

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
set_option maxHeartbeats 3000000
open scoped BigOperators
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankArbitraryRowBranchingOperator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondFullCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondPathCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondResidualSuffixPartition
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondRootCommutator
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSpectralPath
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixCoefficientFactor
namespace MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
theorem _root_.solution
    {r n : ℕ} (lam : Fin (r + 1) → ℕ)
    (target pivot next : Fin (r + 1)) (k : Fin n) :
    (∑ L ∈ (precedingRows pivot).powerset,
      spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
        localSpectralDiamondResidual lam target pivot next k L) =
      spectralDiamondPrefixResidual lam target pivot next k := by
  let T := spectralDiamondResidualTransform lam target pivot next k
  let path (L : Finset (Fin (r + 1))) :
      (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n) ×
        (PolynomialSpace r n →ₗ[ℝ] PolynomialSpace r n) :=
    (diamondPathOperator pivot k L, diamondPathOperator next k L)
  have hlocal (L : Finset (Fin (r + 1))) :
      T (path L) =
        localSpectralDiamondResidual lam target pivot next k L := by
    unfold T path localSpectralDiamondResidual
    exact spectralDiamondResidualTransform_apply lam target pivot next k
      (diamondPathOperator pivot k L) (diamondPathOperator next k L)
  have hsum :
      (∑ L ∈ (precedingRows pivot).powerset,
        spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
          localSpectralDiamondResidual lam target pivot next k L) =
        T (∑ L ∈ (precedingRows pivot).powerset,
          spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
            path L) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro L _
    rw [map_smul, hlocal]
  rw [hsum]
  have hpair :
      (∑ L ∈ (precedingRows pivot).powerset,
        spectralPathCoeff lam pivot (shiftedRowGap lam target pivot + 1) L •
          path L) =
        (spectralPathOperator lam pivot pivot k
          (shiftedRowGap lam target pivot + 1),
          spectralPathOperator lam pivot next k
            (shiftedRowGap lam target pivot + 1)) := by
    apply Prod.ext
    · simp [path, spectralPathOperator, Prod.fst_sum]
    · simp [path, spectralPathOperator, Prod.snd_sum]
  rw [hpair]
  unfold T spectralDiamondPrefixResidual
  exact spectralDiamondResidualTransform_apply lam target pivot next k
    (spectralPathOperator lam pivot pivot k
      (shiftedRowGap lam target pivot + 1))
    (spectralPathOperator lam pivot next k
      (shiftedRowGap lam target pivot + 1))
end MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowSameAxisDiamondSuffixSummation
