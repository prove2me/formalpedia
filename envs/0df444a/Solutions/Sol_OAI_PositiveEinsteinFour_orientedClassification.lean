-- Prove2me | solution 1 for OAI.PositiveEinsteinFour.orientedClassification
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T21:01:07.164991+00:00
-- url     : https://prove2.me/submissions/8c6ddcc4-59e0-424e-9c55-2fb2d6db16a5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_EinsteinFour
import Definitions.Def_OAIQ091C034
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_minusHVariance
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_minusNormVariance
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_normDifferenceVariance
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_one_block_zero_of_variance
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_plusHVariance
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_MetricGreenData_plusNormVariance
import Theorems.Thm_OAI_PositiveEinsteinFour_Geometry_actual_derdzinski_hitchin

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylGeometry
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete orthonormal frames and curvature blocks of the metric in the
classification statement, defined from its chart curvature. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem frameCurvature_sectional (g : SmoothMetric M) (c : M)
    (e : OrthonormalFrame g c) (i j : Fin 4) :
    frameCurvature g c e i j j i =
      sectionalNumerator g c (chartAt FourSpace c c) (e.vector i) (e.vector j) := rfl

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualRicciContraction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction of the actual chart curvature in an orthonormal frame.
This is a finite change-of-basis calculation, used to discharge the Ricci
positivity needed by constant Einstein normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

variable {g : SmoothMetric M} {c : M}

theorem frameCurvature_first_self (e : OrthonormalFrame g c) (i k l : Fin 4) :
    frameCurvature g c e i i k l = 0 := by
  have h := frameCurvature_first_skew e i i k l
  linarith


end
end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_RiemannianVolume
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The measure in the geometric application is fixed by the metric. In four
Euclidean dimensions the diameter-normalized Hausdorff measure is multiplied
by the unit-ball factor `(pi^2 / 2) / 2^4`. Positivity and finiteness are kept
separate from the elementary probability normalization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Bundle
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem volumeRatio_pos {g : SmoothMetric M} (h : FinitePositiveVolume g) :
    0 < volumeRatio g := by
  exact div_pos (totalVolume_pos h) (by positivity)

end

end PositiveEinsteinFour.Geometry

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_MomentObstruction
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A direct polynomial proof of the manuscript's two-constrained-moments
obstruction. The variable `x` is `sqrt(z/2)`. Four rational interval
certificates replace the compact-measure optimization argument. -/

namespace PositiveEinsteinFour.MomentObstruction

open MeasureTheory Filter

noncomputable section

private theorem lower_cert {x : ℝ} (hlo : 0 ≤ x)
    (hhi : x ≤ 1) : 0 ≤ lowerPolynomial x := by
  have hz : 0 ≤ x := by linarith
  have hw : 0 ≤ 1 - x := by linarith
  have hcert : 4050 * (lowerPolynomial x) =
      202500 * (1 - x) ^ 16 +
      3240000 * (x) * (1 - x) ^ 15 +
      24089400 * (x) ^ 2 * (1 - x) ^ 14 +
      110451600 * (x) ^ 3 * (1 - x) ^ 13 +
      349411320 * (x) ^ 4 * (1 - x) ^ 12 +
      808172640 * (x) ^ 5 * (1 - x) ^ 11 +
      1412520120 * (x) ^ 6 * (1 - x) ^ 10 +
      1900681200 * (x) ^ 7 * (1 - x) ^ 9 +
      1986571296 * (x) ^ 8 * (1 - x) ^ 8 +
      1614331008 * (x) ^ 9 * (1 - x) ^ 7 +
      1013073768 * (x) ^ 10 * (1 - x) ^ 6 +
      483298416 * (x) ^ 11 * (1 - x) ^ 5 +
      170408160 * (x) ^ 12 * (1 - x) ^ 4 +
      42313536 * (x) ^ 13 * (1 - x) ^ 3 +
      6779448 * (x) ^ 14 * (1 - x) ^ 2 +
      582768 * (x) ^ 15 * (1 - x) +
      15181 * (x) ^ 16 := by
    unfold lowerPolynomial rootWeight
    ring
  have hp : 0 ≤ 4050 * (lowerPolynomial x) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem dual_cert_0 {x : ℝ} (hlo : 0 ≤ x)
    (hhi : x ≤ 1 / 4) : 0 ≤ dualPolynomial x - 1 / 100 := by
  have hz : 0 ≤ 4 * x - 0 := by linarith
  have hw : 0 ≤ 1 - 4 * x := by linarith
  have hcert : 251658240000 * (dualPolynomial x - 1 / 100) =
      729946521600 * (1 - 4 * x) ^ 13 +
      8451214540800 * (4 * x - 0) * (1 - 4 * x) ^ 12 +
      44734253629440 * (4 * x - 0) ^ 2 * (1 - 4 * x) ^ 11 +
      143206668042240 * (4 * x - 0) ^ 3 * (1 - 4 * x) ^ 10 +
      308991546703872 * (4 * x - 0) ^ 4 * (1 - 4 * x) ^ 9 +
      473869170229248 * (4 * x - 0) ^ 5 * (1 - 4 * x) ^ 8 +
      530527271067648 * (4 * x - 0) ^ 6 * (1 - 4 * x) ^ 7 +
      438134994247680 * (4 * x - 0) ^ 7 * (1 - 4 * x) ^ 6 +
      266251826545920 * (4 * x - 0) ^ 8 * (1 - 4 * x) ^ 5 +
      117245650856032 * (4 * x - 0) ^ 9 * (1 - 4 * x) ^ 4 +
      36244155273088 * (4 * x - 0) ^ 10 * (1 - 4 * x) ^ 3 +
      7423076447728 * (4 * x - 0) ^ 11 * (1 - 4 * x) ^ 2 +
      900827489760 * (4 * x - 0) ^ 12 * (1 - 4 * x) +
      49052866775 * (4 * x - 0) ^ 13 := by
    unfold dualPolynomial rootMoment rootWeight constraint
    ring
  have hp : 0 ≤ 251658240000 * (dualPolynomial x - 1 / 100) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem dual_cert_1 {x : ℝ} (hlo : 1 / 4 ≤ x)
    (hhi : x ≤ 1 / 2) : 0 ≤ dualPolynomial x - 1 / 100 := by
  have hz : 0 ≤ 4 * x - 1 := by linarith
  have hw : 0 ≤ 2 - 4 * x := by linarith
  have hcert : 251658240000 * (dualPolynomial x - 1 / 100) =
      49052866775 * (2 - 4 * x) ^ 13 +
      374547046390 * (4 * x - 1) * (2 - 4 * x) ^ 12 +
      1107711127288 * (4 * x - 1) ^ 2 * (2 - 4 * x) ^ 11 +
      1478028461488 * (4 * x - 1) ^ 3 * (2 - 4 * x) ^ 10 +
      1147777822832 * (4 * x - 1) ^ 4 * (2 - 4 * x) ^ 9 +
      4322397070176 * (4 * x - 1) ^ 5 * (2 - 4 * x) ^ 8 +
      17544214841088 * (4 * x - 1) ^ 6 * (2 - 4 * x) ^ 7 +
      37665583093248 * (4 * x - 1) ^ 7 * (2 - 4 * x) ^ 6 +
      49210071833856 * (4 * x - 1) ^ 8 * (2 - 4 * x) ^ 5 +
      41997049303552 * (4 * x - 1) ^ 9 * (2 - 4 * x) ^ 4 +
      23754829223936 * (4 * x - 1) ^ 10 * (2 - 4 * x) ^ 3 +
      8639408795648 * (4 * x - 1) ^ 11 * (2 - 4 * x) ^ 2 +
      1837678284800 * (4 * x - 1) ^ 12 * (2 - 4 * x) +
      174322229248 * (4 * x - 1) ^ 13 := by
    unfold dualPolynomial rootMoment rootWeight constraint
    ring
  have hp : 0 ≤ 251658240000 * (dualPolynomial x - 1 / 100) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem dual_cert_2 {x : ℝ} (hlo : 1 / 2 ≤ x)
    (hhi : x ≤ 3 / 4) : 0 ≤ dualPolynomial x - 1 / 100 := by
  have hz : 0 ≤ 4 * x - 2 := by linarith
  have hw : 0 ≤ 3 - 4 * x := by linarith
  have hcert : 251658240000 * (dualPolynomial x - 1 / 100) =
      174322229248 * (3 - 4 * x) ^ 13 +
      2694699675648 * (4 * x - 2) * (3 - 4 * x) ^ 12 +
      18923665485824 * (4 * x - 2) ^ 2 * (3 - 4 * x) ^ 11 +
      80014357612544 * (4 * x - 2) ^ 3 * (3 - 4 * x) ^ 10 +
      227502921216512 * (4 * x - 2) ^ 4 * (3 - 4 * x) ^ 9 +
      459761839310592 * (4 * x - 2) ^ 5 * (3 - 4 * x) ^ 8 +
      679967974467072 * (4 * x - 2) ^ 6 * (3 - 4 * x) ^ 7 +
      745642437426432 * (4 * x - 2) ^ 7 * (3 - 4 * x) ^ 6 +
      606556136015712 * (4 * x - 2) ^ 8 * (3 - 4 * x) ^ 5 +
      361621098249552 * (4 * x - 2) ^ 9 * (3 - 4 * x) ^ 4 +
      153606171085104 * (4 * x - 2) ^ 10 * (3 - 4 * x) ^ 3 +
      44020313581224 * (4 * x - 2) ^ 11 * (3 - 4 * x) ^ 2 +
      7626516539478 * (4 * x - 2) ^ 12 * (3 - 4 * x) +
      602961182133 * (4 * x - 2) ^ 13 := by
    unfold dualPolynomial rootMoment rootWeight constraint
    ring
  have hp : 0 ≤ 251658240000 * (dualPolynomial x - 1 / 100) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

private theorem dual_cert_3 {x : ℝ} (hlo : 3 / 4 ≤ x)
    (hhi : x ≤ 1) : 0 ≤ dualPolynomial x - 1 / 100 := by
  have hz : 0 ≤ 4 * x - 3 := by linarith
  have hw : 0 ≤ 4 - 4 * x := by linarith
  have hcert : 251658240000 * (dualPolynomial x - 1 / 100) =
      602961182133 * (4 - 4 * x) ^ 13 +
      8050474195980 * (4 * x - 3) * (4 - 4 * x) ^ 12 +
      49107805459248 * (4 * x - 3) ^ 2 * (4 - 4 * x) ^ 11 +
      181015545999936 * (4 * x - 3) ^ 3 * (4 - 4 * x) ^ 10 +
      449173478536992 * (4 * x - 3) ^ 4 * (4 - 4 * x) ^ 9 +
      790669096672896 * (4 * x - 3) ^ 5 * (4 - 4 * x) ^ 8 +
      1012687566317568 * (4 * x - 3) ^ 6 * (4 - 4 * x) ^ 7 +
      951233732886528 * (4 * x - 3) ^ 7 * (4 - 4 * x) ^ 6 +
      650650258538496 * (4 * x - 3) ^ 8 * (4 - 4 * x) ^ 5 +
      316275247562752 * (4 * x - 3) ^ 9 * (4 - 4 * x) ^ 4 +
      103840494911488 * (4 * x - 3) ^ 10 * (4 - 4 * x) ^ 3 +
      20745409527808 * (4 * x - 3) ^ 11 * (4 - 4 * x) ^ 2 +
      1936726425600 * (4 * x - 3) ^ 12 * (4 - 4 * x) +
      9784524800 * (4 * x - 3) ^ 13 := by
    unfold dualPolynomial rootMoment rootWeight constraint
    ring
  have hp : 0 ≤ 251658240000 * (dualPolynomial x - 1 / 100) := by
    rw [hcert]
    positivity
  nlinarith only [hp]

theorem potential_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    16 * x ^ 4 ≤ potential x := by
  have h := mul_nonneg (sq_nonneg x) (lower_cert hx hx1)
  have hid : potential x - 16 * x ^ 4 = x ^ 2 * lowerPolynomial x := by
    unfold potential rootMoment lowerPolynomial
    ring
  linarith

theorem dual_lower {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    1 / 100 ≤ dualPolynomial x := by
  by_cases h1 : x ≤ 1 / 4
  · linarith [dual_cert_0 hx h1]
  by_cases h2 : x ≤ 1 / 2
  · linarith [dual_cert_1 (by linarith) h2]
  by_cases h3 : x ≤ 3 / 4
  · linarith [dual_cert_2 (by linarith) h3]
  · linarith [dual_cert_3 (by linarith) hx1]

theorem rootMoment_nonneg {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ rootMoment x := by
  have h8 : x ^ 8 ≤ 1 := pow_le_one₀ hx hx1
  have hr : 0 ≤ rootWeight x := by
    unfold rootWeight
    nlinarith [pow_nonneg hx 4]
  exact mul_nonneg hx hr

/-- The pointwise dual inequality, uniform in the scalar mean parameter. -/
theorem dual_bound {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (t : ℝ) :
    1 / 100 ≤ potential x - 64 * t * rootMoment x + 32 * t ^ 2 +
      ((33 / 50) * t - 403 / 2000) * constraint x := by
  have hid : potential x - 64 * t * rootMoment x + 32 * t ^ 2 +
      ((33 / 50) * t - 403 / 2000) * constraint x =
      32 * (t - rootMoment x + (33 / 50) * constraint x / 64) ^ 2 +
        dualPolynomial x := by
    unfold potential dualPolynomial
    ring
  rw [hid]
  nlinarith [sq_nonneg (t - rootMoment x + (33 / 50) * constraint x / 64),
    dual_lower hx hx1]

private theorem integrable_comp_interval {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {x : Ω → ℝ}
    (hxm : AEStronglyMeasurable x μ) (hx : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc (0 : ℝ) 1)
    {f : ℝ → ℝ} (hf : Continuous f) : Integrable (fun ω => f (x ω)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).exists_bound_of_continuousOn hf.continuousOn
  exact (integrable_const C).mono' (hf.comp_aestronglyMeasurable hxm)
    (hx.mono fun ω hω => hC (x ω) hω)

/-- The two-moment obstruction in the coordinate `x = sqrt(z/2)`. The proof
uses the explicit dual polynomial; no compactness or extremal-support input
is assumed. -/
theorem normalized_moment_obstruction {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {x : Ω → ℝ}
    (hxm : AEStronglyMeasurable x μ) (hx : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc (0 : ℝ) 1)
    (hgap : 1 ≤ ∫ ω, 4 * x ω ^ 4 ∂μ)
    (hconstraint : (∫ ω, constraint (x ω) ∂μ) ≤ 0) :
    32 * (∫ ω, rootMoment (x ω) ∂μ) ^ 2 - ∫ ω, potential (x ω) ∂μ < 0 := by
  let t : ℝ := ∫ ω, rootMoment (x ω) ∂μ
  have ih : Integrable (fun ω => rootMoment (x ω)) μ :=
    integrable_comp_interval hxm hx (by unfold rootMoment rootWeight; fun_prop)
  have ip : Integrable (fun ω => potential (x ω)) μ :=
    integrable_comp_interval hxm hx (by unfold potential rootMoment rootWeight; fun_prop)
  have ig : Integrable (fun ω => constraint (x ω)) μ :=
    integrable_comp_interval hxm hx (by unfold constraint; fun_prop)
  have i4 : Integrable (fun ω => x ω ^ 4) μ :=
    integrable_comp_interval (f := fun r : ℝ => r ^ 4) hxm hx (by fun_prop)
  have ht : 0 ≤ t := integral_nonneg_of_ae
    (hx.mono fun ω hω => rootMoment_nonneg hω.1 hω.2)
  have hp : 4 ≤ ∫ ω, potential (x ω) ∂μ := by
    have hlower := integral_mono_ae (i4.const_mul 16) ip
      (hx.mono fun ω hω => potential_lower hω.1 hω.2)
    rw [integral_const_mul] at hgap hlower
    linarith
  by_contra! hJ
  have ht3 : 1 / 3 ≤ t := by
    change 0 ≤ 32 * t ^ 2 - _ at hJ
    nlinarith
  let a : ℝ := (33 / 50) * t - 403 / 2000
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have iF : Integrable (fun ω => potential (x ω) - 64 * t * rootMoment (x ω) +
      32 * t ^ 2 + a * constraint (x ω)) μ :=
    ((ip.sub (ih.const_mul (64 * t))).add (integrable_const (32 * t ^ 2))).add (ig.const_mul a)
  have hF := integral_mono_ae (integrable_const (1 / 100 : ℝ)) iF
    (hx.mono fun ω hω => dual_bound hω.1 hω.2 t)
  have hI : (∫ ω, potential (x ω) - 64 * t * rootMoment (x ω) +
      32 * t ^ 2 + a * constraint (x ω) ∂μ) =
      (∫ ω, potential (x ω) ∂μ) - 32 * t ^ 2 +
        a * ∫ ω, constraint (x ω) ∂μ := by
    have hi1 := integral_add ((ip.sub (ih.const_mul (64 * t))).add
      (integrable_const (32 * t ^ 2))) (ig.const_mul a)
    have hi2 := integral_add (ip.sub (ih.const_mul (64 * t))) (integrable_const (32 * t ^ 2))
    have hi3 := integral_sub ip (ih.const_mul (64 * t))
    simp only [Pi.add_apply, Pi.sub_apply] at hi1 hi2 hi3
    rw [hi1, hi2, hi3]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul]
    change (∫ ω, potential (x ω) ∂μ) - 64 * t * t + 32 * t ^ 2 +
      a * ∫ ω, constraint (x ω) ∂μ = _
    ring
  rw [hI] at hF
  simp only [integral_const, probReal_univ, one_smul] at hF
  have hneg := mul_nonpos_of_nonneg_of_nonpos ha hconstraint
  dsimp [t] at hF
  linarith

theorem H_two_mul_sq {x : ℝ} (hx : 0 ≤ x) :
    H (2 * x ^ 2) = Real.sqrt 2 * rootMoment x := by
  unfold H rootMoment rootWeight
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hx]
  ring

theorem Phi_two_mul_sq {x : ℝ} (hx : 0 ≤ x) :
    Phi (2 * x ^ 2) = potential x := by
  unfold Phi
  rw [H_two_mul_sq hx, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  unfold potential
  ring

/-- The original two-constrained-moments lemma, with no regularity beyond
measurability of the bounded scalar variable. -/
theorem two_constrained_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {z : Ω → ℝ}
    (hzm : AEStronglyMeasurable z μ) (hz : ∀ᵐ ω ∂μ, z ω ∈ Set.Icc (0 : ℝ) 2)
    (hgap : 1 ≤ ∫ ω, z ω ^ 2 ∂μ)
    (hconstraint : (∫ ω, 28 * z ω + 6 * z ω ^ 2 ∂μ) ≤ 25) :
    16 * (∫ ω, H (z ω) ∂μ) ^ 2 - ∫ ω, Phi (z ω) ∂μ < 0 := by
  let x : Ω → ℝ := fun ω => Real.sqrt (z ω / 2)
  have hxm : AEStronglyMeasurable x μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable
      ((continuous_id.div_const (2 : ℝ)).comp_aestronglyMeasurable hzm)
  have hx : ∀ᵐ ω ∂μ, x ω ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hz] with ω hω
    exact ⟨Real.sqrt_nonneg _, (Real.sqrt_le_one).2 (by linarith [hω.2])⟩
  have heq : ∀ᵐ ω ∂μ, z ω = 2 * x ω ^ 2 := by
    filter_upwards [hz] with ω hω
    dsimp [x]
    rw [Real.sq_sqrt (by linarith [hω.1] : 0 ≤ z ω / 2)]
    ring
  have hgap' : 1 ≤ ∫ ω, 4 * x ω ^ 4 ∂μ := by
    have hid : (fun ω => z ω ^ 2) =ᵐ[μ] fun ω => 4 * x ω ^ 4 := by
      filter_upwards [heq] with ω hω
      rw [hω]
      ring
    rwa [integral_congr_ae hid] at hgap
  have ig : Integrable (fun ω => constraint (x ω)) μ :=
    integrable_comp_interval hxm hx (by unfold constraint; fun_prop)
  have hconstraint' : (∫ ω, constraint (x ω) ∂μ) ≤ 0 := by
    have hid : (fun ω => 28 * z ω + 6 * z ω ^ 2) =ᵐ[μ]
        fun ω => constraint (x ω) + 25 := by
      filter_upwards [heq] with ω hω
      rw [hω]
      unfold constraint
      ring
    rw [integral_congr_ae hid, integral_add ig (integrable_const _)] at hconstraint
    simp only [integral_const, probReal_univ, one_smul] at hconstraint
    linarith
  have hmain := normalized_moment_obstruction hxm hx hgap' hconstraint'
  have hH : (fun ω => H (z ω)) =ᵐ[μ]
      fun ω => Real.sqrt 2 * rootMoment (x ω) := by
    filter_upwards [heq, hx] with ω hω hxω
    rw [hω, H_two_mul_sq hxω.1]
  have hPhi : (fun ω => Phi (z ω)) =ᵐ[μ] fun ω => potential (x ω) := by
    filter_upwards [heq, hx] with ω hω hxω
    rw [hω, Phi_two_mul_sq hxω.1]
  rw [integral_congr_ae hH, integral_congr_ae hPhi, integral_const_mul, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith only [hmain]

end

end PositiveEinsteinFour.MomentObstruction

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates01
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The pointwise sectional curvature criterion.

Gursky--LeBrun, `On Einstein Manifolds of Positive Sectional Curvature`
(1999), Lemma 1 proof, equation (5), pp.4--5, arXiv:math/9807055.
For Einstein curvature the minimum sectional curvature is half of
`s/6 + lambda_plus + lambda_minus`. At Ric=3g, strict positivity says
the negatives of the two minimum eigenvalues have sum less than two.
The positive-semidefinite formulation below is that local specialization.
 -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

variable {g : SmoothMetric M} {μ : MeasureTheory.Measure (FrameBundle g)}

theorem shiftedCurvaturePositive_of_published
    (h : GurskyLeBrunSectionalInput g) (hRic : RicciThree g)
    (hsec : HasPositiveSectionalCurvature g) : ShiftedCurvaturePositive g := by
  intro e
  obtain ⟨x, y, hx, hy, hxy⟩ := h hRic hsec e
  exact ⟨x, y, hx, hy, hxy.le⟩

theorem strict_norm_pinching_of_published (d : MetricGreenData g μ)
    (o : OppositeWeylData d) (h : GurskyLeBrunSectionalInput g)
    (hRic : RicciThree g) (hsec : HasPositiveSectionalCurvature g) (e : FrameBundle g) :
    normalizedBlockNorm (plusWeyl g e.base e.frame) +
      normalizedBlockNorm (minusWeyl g e.base e.frame) < 2 := by
  obtain ⟨x, y, hx, hy, hxy⟩ := h hRic hsec e
  have hp := QuaternionFrame.normalizedBlockNorm_le_shift _ (d.weyl.symmetric e)
    (d.weyl.traceFree e) x hx
  have hm := QuaternionFrame.normalizedBlockNorm_le_shift _ (o.symmetric e)
    (o.traceFree e) y hy
  linarith only [hp, hm, hxy]

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Moments
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integer reduction in the balanced-Weyl-moment argument.
Volume is normalized so that the Euler identity is
`2 + n + m = volume * (1 + P + Q)`. -/

namespace PositiveEinsteinFour

noncomputable section

/-- The characteristic identities, two gaps, and upper volume estimate leave
only the ordered exceptional pair `(n₊, n₋) = (2, 1)` if the counts differ. -/
theorem ordered_harmonic_counts (n m : ℕ) (P Q volume : ℝ)
    (hP : 1 ≤ P) (hQ : 1 ≤ Q) (horder : Q ≤ P) (hsum : P + Q < 4)
    (hvolume : 0 < volume)
    (hupper : volume ≤ 2 * (1 - 3 / 40 * (P + Q)))
    (heuler : 2 + (n : ℝ) + (m : ℝ) = volume * (1 + P + Q))
    (hsignature : (n : ℝ) - (m : ℝ) = 2 / 3 * volume * (P - Q)) :
    n = m ∨ n = 2 ∧ m = 1 := by
  have hnm : m ≤ n := by
    have hdiff : 0 ≤ (n : ℝ) - (m : ℝ) := by
      rw [hsignature]
      exact mul_nonneg (mul_nonneg (by norm_num) hvolume.le) (sub_nonneg.mpr horder)
    exact_mod_cast sub_nonneg.mp hdiff
  have hchi : 2 + (n : ℝ) + (m : ℝ) < 7 := by
    have hmul := mul_le_mul_of_nonneg_right hupper
      (show 0 ≤ 1 + P + Q by linarith)
    have hstrict : 0 < (4 - (P + Q)) * (25 - 3 * (P + Q)) := by
      apply mul_pos <;> linarith
    nlinarith [heuler]
  have hratio : 15 * ((n : ℝ) - (m : ℝ)) < 4 * (2 + (n : ℝ) + (m : ℝ)) := by
    have hlin : 10 * (P - Q) < 4 * (1 + P + Q) := by linarith
    have hmul := mul_lt_mul_of_pos_left hlin hvolume
    nlinarith [heuler, hsignature]
  have hnat_sum : 2 + n + m < 7 := by exact_mod_cast hchi
  have hnat_ratio : 15 * (n - m) < 4 * (2 + n + m) := by
    have hcast : (15 * (n - m) : ℕ) < (4 * (2 + n + m) : ℕ) := by
      exact_mod_cast (show 15 * ((n - m : ℕ) : ℝ) <
          4 * (((2 + n + m : ℕ) : ℝ)) by
        push_cast
        rw [Nat.cast_sub hnm]
        exact hratio)
    exact hcast
  omega

/-- In the exceptional count pair, the larger second moment is fixed by the
smaller one. This is the exact `13/7` relation used before the two-moment
obstruction. -/
theorem exceptional_moment_relation (P Q volume : ℝ)
    (heuler : 5 = volume * (1 + P + Q))
    (hsignature : 1 = 2 / 3 * volume * (P - Q)) :
    P = (13 * Q + 3) / 7 := by
  have hvolume_ne : volume ≠ 0 := by
    intro hzero
    simp [hzero] at heuler
  have hprod : volume * (7 * P - 13 * Q - 3) = 0 := by
    nlinarith [heuler, hsignature]
  have := (mul_eq_zero.mp hprod).resolve_left hvolume_ne
  linarith

/-- Integrating `v² ≤ (2-b)²` with the exceptional relation yields the second
constraint of the scalar moment obstruction. `mean` is the mean of `b`. -/
theorem exceptional_moment_constraint (P Q mean : ℝ)
    (hrelation : P = (13 * Q + 3) / 7)
    (hpointwise_integral : P ≤ 4 - 4 * mean + Q) :
    28 * mean + 6 * Q ≤ 25 := by
  linarith

end

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_Balanced
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar assembly of the balanced-Weyl-moments argument. The upper
volume estimate and the weighted variance estimate remain separate geometric
obligations; neither is declared to be a published input here. -/

namespace PositiveEinsteinFour

open MeasureTheory Filter MomentObstruction

noncomputable section

private theorem J_nonneg_of_variance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {z : Ω → ℝ}
    (hzi : Integrable z μ) (hz2i : Integrable (fun ω => z ω ^ 2) μ)
    (hHi : Integrable (fun ω => H (z ω) ^ 2) μ)
    (hvar : (∫ ω, H (z ω) ^ 2 ∂μ) - (∫ ω, H (z ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, z ω ^ 2 ∂μ) - ∫ ω, z ω ∂μ)) :
    0 ≤ 16 * (∫ ω, H (z ω) ∂μ) ^ 2 - ∫ ω, Phi (z ω) ∂μ := by
  have hid : (fun ω => Phi (z ω)) =
      (fun ω => 16 * H (z ω) ^ 2 + 9 * z ω - 9 * z ω ^ 2) := by
    funext ω
    unfold Phi
    ring
  have hi1 := integral_sub ((hHi.const_mul 16).add (hzi.const_mul 9)) (hz2i.const_mul 9)
  have hi2 := integral_add (hHi.const_mul 16) (hzi.const_mul 9)
  simp only [Pi.add_apply] at hi1
  rw [hid, hi1, hi2]
  simp only [integral_const_mul]
  linarith

/-- In the ordered case, the exact integer and moment constraints force equal
moments once the two-constrained-moments obstruction is applied. -/
theorem ordered_balanced_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {v b : Ω → ℝ}
    (n m : ℕ) (volume : ℝ)
    (hbm : AEStronglyMeasurable b μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Set.Icc (0 : ℝ) 2)
    (hb : ∀ᵐ ω ∂μ, b ω ∈ Set.Icc (0 : ℝ) 2)
    (hsum : ∀ᵐ ω ∂μ, v ω + b ω ≤ 2)
    (hbi : Integrable b μ)
    (hv2i : Integrable (fun ω => v ω ^ 2) μ)
    (hb2i : Integrable (fun ω => b ω ^ 2) μ)
    (hHbi : Integrable (fun ω => H (b ω) ^ 2) μ)
    (hvgap : 1 ≤ ∫ ω, v ω ^ 2 ∂μ) (hbgap : 1 ≤ ∫ ω, b ω ^ 2 ∂μ)
    (horder : (∫ ω, b ω ^ 2 ∂μ) ≤ ∫ ω, v ω ^ 2 ∂μ)
    (hmoments : (∫ ω, v ω ^ 2 ∂μ) + (∫ ω, b ω ^ 2 ∂μ) < 4)
    (hvolume : 0 < volume)
    (hupper : volume ≤ 2 * (1 - 3 / 40 *
      ((∫ ω, v ω ^ 2 ∂μ) + ∫ ω, b ω ^ 2 ∂μ)))
    (heuler : 2 + (n : ℝ) + (m : ℝ) = volume *
      (1 + (∫ ω, v ω ^ 2 ∂μ) + ∫ ω, b ω ^ 2 ∂μ))
    (hsignature : (n : ℝ) - (m : ℝ) = 2 / 3 * volume *
      ((∫ ω, v ω ^ 2 ∂μ) - ∫ ω, b ω ^ 2 ∂μ))
    (hvariance : (∫ ω, H (b ω) ^ 2 ∂μ) - (∫ ω, H (b ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, b ω ^ 2 ∂μ) - ∫ ω, b ω ∂μ)) :
    (∫ ω, v ω ^ 2 ∂μ) = (∫ ω, b ω ^ 2 ∂μ) := by
  rcases ordered_harmonic_counts n m _ _ volume hvgap hbgap horder hmoments
    hvolume hupper heuler hsignature with hcounts | ⟨hn, hm⟩
  · have hnreal : (n : ℝ) = (m : ℝ) := congrArg Nat.cast hcounts
    have hprod : volume * ((∫ ω, v ω ^ 2 ∂μ) - ∫ ω, b ω ^ 2 ∂μ) = 0 := by
      rw [hnreal] at hsignature
      linarith
    have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt hvolume)
    linarith
  · subst n
    subst m
    norm_num at heuler hsignature
    have hrelation := exceptional_moment_relation _ _ volume heuler hsignature
    have hi : Integrable (fun ω => 4 - 4 * b ω + b ω ^ 2) μ :=
      ((integrable_const 4).sub (hbi.const_mul 4)).add hb2i
    have hbound : (∫ ω, v ω ^ 2 ∂μ) ≤ 4 - 4 * (∫ ω, b ω ∂μ) + ∫ ω, b ω ^ 2 ∂μ := by
      have h := integral_mono_ae hv2i hi (by
        filter_upwards [hv, hb, hsum] with ω hvω hbω hsω
        have hp : 0 ≤ (2 - b ω - v ω) * (2 - b ω + v ω) := by
          apply mul_nonneg <;> linarith [hvω.1, hbω.2]
        nlinarith)
      have hi1 := integral_add ((integrable_const (4 : ℝ)).sub (hbi.const_mul 4)) hb2i
      have hi2 := integral_sub (integrable_const (4 : ℝ)) (hbi.const_mul 4)
      simp only [Pi.sub_apply] at hi1
      rw [hi1, hi2] at h
      simpa only [integral_const_mul, integral_const, probReal_univ, one_smul] using h
    have hconstraint := exceptional_moment_constraint _ _ _ hrelation hbound
    have hconstraint' : (∫ ω, 28 * b ω + 6 * b ω ^ 2 ∂μ) ≤ 25 := by
      rw [integral_add (hbi.const_mul 28) (hb2i.const_mul 6)]
      simpa only [integral_const_mul] using hconstraint
    have hnegative := two_constrained_moments hbm hb hbgap hconstraint'
    have hnonnegative := J_nonneg_of_variance hbi hb2i hHbi hvariance
    linarith

/-- Symmetric scalar form of the balanced-moment conclusion. The geometric
volume and weighted-variance estimates are explicit premises, pending their
independent formalization. -/
theorem balanced_moments {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {v b : Ω → ℝ}
    (n m : ℕ) (volume : ℝ)
    (hvm : AEStronglyMeasurable v μ) (hbm : AEStronglyMeasurable b μ)
    (hv : ∀ᵐ ω ∂μ, v ω ∈ Set.Icc (0 : ℝ) 2)
    (hb : ∀ᵐ ω ∂μ, b ω ∈ Set.Icc (0 : ℝ) 2)
    (hsum : ∀ᵐ ω ∂μ, v ω + b ω ≤ 2)
    (hvi : Integrable v μ) (hbi : Integrable b μ)
    (hv2i : Integrable (fun ω => v ω ^ 2) μ)
    (hb2i : Integrable (fun ω => b ω ^ 2) μ)
    (hHvi : Integrable (fun ω => H (v ω) ^ 2) μ)
    (hHbi : Integrable (fun ω => H (b ω) ^ 2) μ)
    (hvgap : 1 ≤ ∫ ω, v ω ^ 2 ∂μ) (hbgap : 1 ≤ ∫ ω, b ω ^ 2 ∂μ)
    (hmoments : (∫ ω, v ω ^ 2 ∂μ) + (∫ ω, b ω ^ 2 ∂μ) < 4)
    (hvolume : 0 < volume)
    (hupper : volume ≤ 2 * (1 - 3 / 40 *
      ((∫ ω, v ω ^ 2 ∂μ) + ∫ ω, b ω ^ 2 ∂μ)))
    (heuler : 2 + (n : ℝ) + (m : ℝ) = volume *
      (1 + (∫ ω, v ω ^ 2 ∂μ) + ∫ ω, b ω ^ 2 ∂μ))
    (hsignature : (n : ℝ) - (m : ℝ) = 2 / 3 * volume *
      ((∫ ω, v ω ^ 2 ∂μ) - ∫ ω, b ω ^ 2 ∂μ))
    (hvvariance : (∫ ω, H (v ω) ^ 2 ∂μ) - (∫ ω, H (v ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, v ω ^ 2 ∂μ) - ∫ ω, v ω ∂μ))
    (hbvariance : (∫ ω, H (b ω) ^ 2 ∂μ) - (∫ ω, H (b ω) ∂μ) ^ 2 ≤
      9 / 16 * ((∫ ω, b ω ^ 2 ∂μ) - ∫ ω, b ω ∂μ)) :
    (∫ ω, v ω ^ 2 ∂μ) = (∫ ω, b ω ^ 2 ∂μ) ∧ n = m := by
  have hequal : (∫ ω, v ω ^ 2 ∂μ) = (∫ ω, b ω ^ 2 ∂μ) := by
    rcases le_total (∫ ω, b ω ^ 2 ∂μ) (∫ ω, v ω ^ 2 ∂μ) with horder | horder
    · exact ordered_balanced_moments n m volume hbm hv hb hsum hbi hv2i hb2i hHbi
        hvgap hbgap horder hmoments hvolume hupper heuler hsignature hbvariance
    · symm
      apply ordered_balanced_moments m n volume hvm hb hv
        (hsum.mono fun ω hω => by linarith) hvi hb2i hv2i hHvi hbgap hvgap horder
        (by linarith) hvolume (by convert hupper using 1; ring)
        (by nlinarith [heuler]) (by nlinarith [hsignature]) hvvariance
  refine ⟨hequal, ?_⟩
  rw [hequal] at hsignature
  have hreal : (n : ℝ) = (m : ℝ) := by linarith
  exact_mod_cast hreal

end

end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ClassificationScaling
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Angular.instCompactSpaceDirections _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.canonicalFrameMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.canonicalUnitTangentMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.chartCoordinateMeasure_sigmaFinite _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_pseudoMetrizable _root_.OAI.PositiveEinsteinFour.Geometry.frameBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instBorelSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothH1TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instCoeSmoothL2TwoFormSubtypeForallTwoFormFourMemSubmoduleRealSmoothTwoForms _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instMeasurableSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNonemptyOrthonormalFrame _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instT2SpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceFrameBundle _root_.OAI.PositiveEinsteinFour.Geometry.instTopologicalSpaceUnitTangentBundle _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_chartedSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_compactSpace _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_isManifold _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_nonempty _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t2Space _root_.OAI.PositiveEinsteinFour.Geometry.orientationCover_t3Space _root_.OAI.PositiveEinsteinFour.Geometry.orientedFiberMeasure_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarAngularProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.polarDirectionProbability_probability _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothH1TwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothTwoFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.symmetricFrameMeasure_finite _root_.OAI.PositiveEinsteinFour.Geometry.tangentBundle_secondCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite _root_.OAI.PositiveEinsteinFour.Geometry.unitTangentBundle_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the exact metric classification across the classical
constant-rescaling identity for Riemannian distance. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem scaledEDistance_mul (g : SmoothMetric M) (a b : ℝ) (ha : 0 ≤ a)
    (x y : M) :
    scaledEDistance g (a * b) x y =
      ENNReal.ofReal (Real.sqrt a) * scaledEDistance g b x y := by
  simp only [scaledEDistance, Real.sqrt_mul ha, ENNReal.ofReal_mul (Real.sqrt_nonneg a),
    mul_assoc]

end
end PositiveEinsteinFour

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_WeylEstimates03
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.chartBaseDensity_sfinite _root_.OAI.PositiveEinsteinFour.Geometry.instAddCommGroupSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instAddSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instCoeOutSmoothL2OneFormSubtypeForallCovariantCoordinatesOfNatNatMemSubmoduleRealSmoothCovariantFields _root_.OAI.PositiveEinsteinFour.Geometry.instModuleRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instNegSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulIntSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulNatSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSMulRealSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instSubSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.instZeroSmoothL2OneForm _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1MeanZero_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1_complete _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerCore _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormInnerProductSpace _root_.OAI.PositiveEinsteinFour.Geometry.smoothOneFormNormedAddCommGroup _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.mem_scalarH1MeanZero _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_first _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Gradient_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Mean_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1SubtractMean_idempotent _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_one _root_.OAI.PositiveEinsteinFour.Geometry.scalarH1Value_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_equiv _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedH1ToH1_smooth _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_none _root_.OAI.PositiveEinsteinFour.Geometry.scalarWeightedJetEquiv_some _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradientL2_subtractMean _root_.OAI.PositiveEinsteinFour.Geometry.smoothScalarGradient_subtractMean
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Characteristic-number and Weyl-gap identities. Gursky--LeBrun, equations (6)--(7), together with the degree
one Bochner vanishing and Hodge decomposition (Petersen §9.1), give the two
integer-count identities. Gursky--LeBrun Theorem 1 gives the two norm gaps.
 -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

theorem BrinKarcherAveraging.base_integral (hμ : BrinKarcherAveraging g μ)
    (h : Angular.FollandMoments) (A : M → ℝ)
    (hi : Integrable (fun e : FrameBundle g => A e.base) μ)
    (ha : Integrable A (normalizedVolume g)) :
    (∫ e, A e.base ∂μ) = ∫ c, A c ∂normalizedVolume g := by
  let : IsProbabilityMeasure Angular.sphereMeasure := h.probability
  apply hμ.fiberFormula _ _ hi ha
  · intro e f hef _
    exact congrArg A hef
  · intro c e
    change (∫ _ : Angular.Directions, A c ∂Angular.sphereMeasure) = A c
    simp

theorem norm_square_frame_integrals {orientation : FrameOrientation g}
    (hμ : BrinKarcherAveraging g μ) (hF : Angular.FollandMoments)
    (h : PetersenOrientedNormInput orientation) (hae : ∀ᵐ e ∂μ, e ∈ orientation.positive)
    (hpi : Integrable (fun e : FrameBundle g => normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) μ)
    (hmi : Integrable (fun e : FrameBundle g => normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) μ)
    (hp : Integrable (fun c => plusNorm orientation c ^ 2) (normalizedVolume g))
    (hm : Integrable (fun c => minusNorm orientation c ^ 2) (normalizedVolume g)) :
    ((∫ e, normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2 ∂μ) =
      ∫ c, plusNorm orientation c ^ 2 ∂normalizedVolume g) ∧
    ((∫ e, normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2 ∂μ) =
      ∫ c, minusNorm orientation c ^ 2 ∂normalizedVolume g) := by
  have hep : (fun e : FrameBundle g => normalizedBlockNorm (plusWeyl g e.base e.frame) ^ 2) =ᵐ[μ]
      fun e => plusNorm orientation e.base ^ 2 := by
    filter_upwards [hae] with e he
    rw [h.plusFrame e he]
  have hem : (fun e : FrameBundle g => normalizedBlockNorm (minusWeyl g e.base e.frame) ^ 2) =ᵐ[μ]
      fun e => minusNorm orientation e.base ^ 2 := by
    filter_upwards [hae] with e he
    rw [h.minusFrame e he]
  exact ⟨(integral_congr_ae hep).trans
      (hμ.base_integral hF _ (hpi.congr hep) hp),
    (integral_congr_ae hem).trans (hμ.base_integral hF _ (hmi.congr hem) hm)⟩

end
end PositiveEinsteinFour.Geometry
end


section

/-! The Weyl norm gap follows from the regularized energy estimate and
the sharp scalar Sobolev inequality. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory Set Filter
open scoped BigOperators Manifold ContDiff _root_.Topology

noncomputable section

section Probability

variable {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  [CompactSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem continuous_integral_cauchy_schwarz (v F : C(Ω, ℝ)) (hv : ∀ x, 0 ≤ v x) :
    (∫ x, v x * F x ^ 2 ∂μ) ≤
      Real.sqrt (∫ x, v x ^ 2 ∂μ) * Real.sqrt (∫ x, F x ^ 4 ∂μ) := by
  have hm₁ : MemLp (fun x => v x) (ENNReal.ofReal (2 : ℝ)) μ :=
    v.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm₂ : MemLp (fun x => F x ^ 2) (ENNReal.ofReal (2 : ℝ)) μ :=
    (F.continuous.pow 2).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hv)
    (Filter.Eventually.of_forall (fun x => sq_nonneg (F x))) hm₁ hm₂
  simpa only [Real.rpow_two, ← Real.sqrt_eq_rpow, ← pow_mul,
    show (2 : ℕ) * 2 = 4 by norm_num] using h

/-- A uniform positive fourth moment and arbitrarily small regularization
errors turn the sharp scalar inequality into a norm gap. -/
theorem norm_gap_of_regularized_sobolev (v : C(Ω, ℝ)) (F : ℝ → C(Ω, ℝ))
    (E : ℝ → ℝ) (hv : ∀ x, 0 ≤ v x) (c : ℝ) (hc : 0 < c)
    (hminorant : ∀ ε > 0, c ≤ ∫ x, F ε x ^ 4 ∂μ)
    (hsob : ∀ ε > 0, Real.sqrt (∫ x, F ε x ^ 4 ∂μ) ≤
      (∫ x, F ε x ^ 2 ∂μ) + E ε / 2)
    (henergy : ∀ ε > 0, E ε + 2 * (∫ x, F ε x ^ 2 ∂μ) ≤
      2 * (∫ x, v x * F ε x ^ 2 ∂μ) + 2 * ε ^ (2 / 3 : ℝ)) :
    1 ≤ ∫ x, v x ^ 2 ∂μ := by
  by_contra hgap
  have hB : Real.sqrt (∫ x, v x ^ 2 ∂μ) < 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_lt_sqrt
      (integral_nonneg (fun x => sq_nonneg (v x))) (lt_of_not_ge hgap)
  have hfixed : 0 < (1 - Real.sqrt (∫ x, v x ^ 2 ∂μ)) * Real.sqrt c :=
    mul_pos (sub_pos.mpr hB) (Real.sqrt_pos.mpr hc)
  have hbound (ε : ℝ) (hε : 0 < ε) :
      (1 - Real.sqrt (∫ x, v x ^ 2 ∂μ)) * Real.sqrt c ≤ ε ^ (2 / 3 : ℝ) := by
    have hs := hsob ε hε
    have he := henergy ε hε
    have hcs := continuous_integral_cauchy_schwarz μ v (F ε) hv
    have hlo := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hminorant ε hε))
      (sub_pos.mpr hB).le
    nlinarith only [hs, he, hcs, hlo]
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have ht : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht' : Tendsto (fun n => ε n ^ (2 / 3 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)] using
      ht.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 3))
  have hn := ge_of_tendsto ht' (Filter.Eventually.of_forall (fun n => hbound (ε n) (hε n)))
  linarith

end Probability

theorem regularizedWeylRoot_fourth_lower (ε : ℝ) (A : Mat) :
    normalizedBlockNorm A ^ (4 / 3 : ℝ) ≤ regularizedWeylRoot ε A ^ 4 := by
  have h := Real.rpow_le_rpow (normalizedBlockNorm_nonneg A)
    (norm_le_regularizedBlockNorm ε A) (by norm_num : (0 : ℝ) ≤ 4 / 3)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  unfold regularizedWeylRoot
  have hu : 0 ≤ regularizedBlockNorm ε A := Real.sqrt_nonneg _
  rw [← Real.rpow_mul_natCast hu]
  norm_num

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance weylGapFrameCompact (g : SmoothMetric M) : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g

theorem canonical_plusNorm_moment (g : SmoothMetric M) (o : FrameOrientation g)
    (p : ℝ) (hp : 0 ≤ p) :
    (∫ e : FrameBundle g, normalizedBlockNorm (plusWeyl g e.base e.frame) ^ p
      ∂canonicalFrameMeasure g o) = ∫ x, plusNorm o x ^ p ∂normalizedVolume g := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  have hcont := (continuous_plusNorm g o).rpow_const (fun _ => Or.inr hp)
  calc
    _ = ∫ e : FrameBundle g, plusNorm o e.base ^ p ∂canonicalFrameMeasure g o := by
      apply integral_congr_ae
      filter_upwards [canonicalFrameMeasure_supported g o] with e he
      rw [actual_plusNorm_frame o e he]
    _ = _ := canonicalFrameMeasure_integral_base g o _
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

/-- The sharp Sobolev premise is exposed explicitly. All other ingredients
are the actual Weyl equation, canonical measure, and regularized energy. -/
theorem plus_gap_of_regularized_sharp_sobolev (g : SmoothMetric M) (o : FrameOrientation g)
    (d : MetricGreenData g (canonicalFrameMeasure g o))
    (hsob : ∀ (ε : ℝ) (hε : 0 < ε),
      Real.sqrt (∫ e, d.weylRootField ε e ^ 4 ∂canonicalFrameMeasure g o) ≤
        (∫ e, d.weylRootField ε e ^ 2 ∂canonicalFrameMeasure g o) +
          (∫ e, ∑ i, d.weylRootFirstField ε hε i e ^ 2
            ∂canonicalFrameMeasure g o) / 2)
    (hnonzero : ∃ x, plusNorm o x ≠ 0) :
    1 ≤ ∫ x, plusNorm o x ^ 2 ∂normalizedVolume g := by
  let : IsProbabilityMeasure (normalizedVolume g) :=
    normalizedVolume_isProbability (actual_finitePositiveVolume g)
  let μ := canonicalFrameMeasure g o
  let v : C(FrameBundle g, ℝ) := d.plusNormField
  let F : ℝ → C(FrameBundle g, ℝ) := d.weylRootField
  let E : ℝ → ℝ := fun ε => if hε : 0 < ε then
    ∫ e, ∑ i, d.weylRootFirstField ε hε i e ^ 2 ∂μ else 0
  let c := ∫ x, plusNorm o x ^ (4 / 3 : ℝ) ∂normalizedVolume g
  have hc : 0 < c := by
    let := normalizedVolume_isOpenPosMeasure g
    obtain ⟨x, hx⟩ := hnonzero
    have hcont := (continuous_plusNorm g o).rpow_const
      (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 4 / 3))
    apply integral_pos_of_integrable_nonneg_nonzero hcont
      (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (fun x => Real.rpow_nonneg (plusNorm_nonneg o x) _)
    exact (Real.rpow_pos_of_pos (lt_of_le_of_ne (plusNorm_nonneg o x) (Ne.symm hx)) _).ne'
  have hm (ε : ℝ) (_hε : 0 < ε) : c ≤ ∫ e, F ε e ^ 4 ∂μ := by
    dsimp only [c]
    rw [← canonical_plusNorm_moment g o (4 / 3 : ℝ) (by norm_num)]
    apply integral_mono
      (((d.plusNormField.continuous).rpow_const
        (fun _ => Or.inr (by norm_num : (0 : ℝ) ≤ 4 / 3))).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))
      (((F ε).continuous.pow 4).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    intro e
    exact regularizedWeylRoot_fourth_lower ε (plusWeyl g e.base e.frame)
  have hs (ε : ℝ) (hε : 0 < ε) : Real.sqrt (∫ e, F ε e ^ 4 ∂μ) ≤
      (∫ e, F ε e ^ 2 ∂μ) + E ε / 2 := by
    simpa only [E, dite_eq_left hε] using hsob ε hε
  have he (ε : ℝ) (hε : 0 < ε) : E ε + 2 * (∫ e, F ε e ^ 2 ∂μ) ≤
      2 * (∫ e, v e * F ε e ^ 2 ∂μ) + 2 * ε ^ (2 / 3 : ℝ) := by
    have h := d.weylRoot_energy_le ε hε
    have hi₁ : Integrable (fun e => ∑ i, d.weylRootFirstField ε hε i e ^ 2) μ :=
      (continuous_finsetSum _ (fun i _ => (d.weylRootFirstField ε hε i).continuous.pow 2))
        |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi₂ : Integrable (fun e => 2 * F ε e ^ 2) μ :=
      (((F ε).continuous.pow 2).const_mul 2).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_add hi₁ hi₂, integral_const_mul] at h
    simpa only [E, dite_eq_left hε, probReal_univ, mul_one, v,
      MetricGreenData.plusNormField, MetricGreenData.plusMatrixMap,
      ContinuousMap.coe_mk] using h
  have h := norm_gap_of_regularized_sobolev μ v F E
    (fun e => normalizedBlockNorm_nonneg _) c hc hm hs he
  have hmoment : (∫ e, v e ^ 2 ∂μ) =
      ∫ x, plusNorm o x ^ 2 ∂normalizedVolume g := by
    simpa only [Real.rpow_two, v, MetricGreenData.plusNormField,
      MetricGreenData.plusMatrixMap, ContinuousMap.coe_mk] using
      canonical_plusNorm_moment g o 2 (by norm_num)
  rwa [hmoment] at h

end
end PositiveEinsteinFour.Geometry
end


section

/-! Transfer the proved radial volume deficit and the precisely published
global identities to the actual oriented-frame moments. The scalar balanced
moment theorem is then applied without a further volume or moment premise. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {g : SmoothMetric M} {μ : Measure (FrameBundle g)}

variable [CompactSpace (FrameBundle g)] [IsProbabilityMeasure μ]

omit [T3Space M] [MeasurableSpace M] [BorelSpace M] in
theorem frame_norm_moment_sum_lt_four (d : MetricGreenData g μ)
    (o : OppositeWeylData d)
    (hpinch : ∀ e, d.plusNormField e + d.minusNormField o e < 2) :
    (∫ e, d.plusNormField e ^ 2 ∂μ) + (∫ e, d.minusNormField o e ^ 2 ∂μ) < 4 := by
  let f : FrameBundle g → ℝ := fun e => d.plusNormField e ^ 2 + d.minusNormField o e ^ 2
  have hf : Continuous f := (d.plusNormField.continuous.pow 2).add
    ((d.minusNormField o).continuous.pow 2)
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hpoint (e : FrameBundle g) : f e < 4 := by
    have hv : 0 ≤ d.plusNormField e := normalizedBlockNorm_nonneg _
    have hb : 0 ≤ d.minusNormField o e := normalizedBlockNorm_nonneg _
    have hs := hpinch e
    have hm := mul_nonneg hv hb
    have ht := mul_pos (by linarith : 0 < 2 - (d.plusNormField e + d.minusNormField o e))
      (by linarith : 0 < 2 + (d.plusNormField e + d.minusNormField o e))
    dsimp only [f]
    nlinarith only [hm, ht]
  let : Nonempty (FrameBundle g) := nonempty_of_isProbabilityMeasure μ
  obtain ⟨e, _, he⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.continuousOn
  have hint : (∫ a, f a ∂μ) ≤ f e := by
    calc
      _ ≤ ∫ _, f e ∂μ := integral_mono_ae hfi (integrable_const _) (by
        filter_upwards [] with a
        exact he (Set.mem_univ a))
      _ = f e := by simp
  have hiP := (d.plusNormField.continuous.pow 2).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hiM := ((d.minusNormField o).continuous.pow 2).integrable_of_hasCompactSupport
    (μ := μ) (HasCompactSupport.of_compactSpace _)
  have hsum : (∫ a, f a ∂μ) =
      (∫ a, d.plusNormField a ^ 2 ∂μ) + ∫ a, d.minusNormField o a ^ 2 ∂μ :=
    integral_add hiP hiM
  rw [hsum] at hint
  exact hint.trans_lt (hpoint e)

end
end PositiveEinsteinFour.Geometry
end


section

/-! The constant rescaling step. The precise classical inputs are the Ricci
contraction of positive sectional curvature (Petersen §3.1.1), and Exercise
3.4.18, p.88, together with the length definition in §1.2. Only the actual
four-dimensional metric, one Ricci diagonal entry, and positive constant
rescalings are used here. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem einstein_of_ricciThree {g : SmoothMetric M} (h : RicciThree g) : IsEinstein g := by
  refine ⟨3, ?_⟩
  intro x i j
  exact congrFun (congrFun (h x) i) j

theorem normalized_oriented_metric [Nonempty M] (g : SmoothMetric M)
    (orientation : FrameOrientation g) (hpositiveRicci : PetersenPositiveRicciInput g)
    (hscaling : PetersenScalingInput g) (hEinstein : IsEinstein g)
    (hpositive : HasPositiveSectionalCurvature g) :
    ∃ (h : SmoothMetric M) (_ : FrameOrientation h) (c : ℝ), 0 < c ∧
      RicciThree h ∧ HasPositiveSectionalCurvature h ∧
      ∀ x y, scaledEDistance h 1 x y = scaledEDistance g c x y := by
  obtain ⟨lam, hlam⟩ := hEinstein
  have hlampos : 0 < lam := by
    let x : M := Classical.choice inferInstance
    have hp := hpositiveRicci hpositive x
    have hg := (chartMetric_posDef g x).diag_pos (i := (0 : Fin 4))
    have he := hlam x 0 0
    change chartRicci g x 0 0 = lam * chartMetric g x 0 0 at he
    nlinarith
  obtain ⟨h, hm, hr, hs, hd, ho⟩ := hscaling (lam / 3) (by positivity)
  obtain ⟨o⟩ := ho orientation
  refine ⟨h, o, lam / 3, by positivity, ?_, ?_, hd⟩
  · intro x
    ext i j
    have he := hlam x i j
    change chartRicci g x i j = lam * chartMetric g x i j at he
    rw [hr, hm]
    change chartRicci g x i j = 3 * (lam / 3 * chartMetric g x i j)
    rw [he]
    ring
  · intro x u v huv
    rw [hs]
    exact mul_pos (by positivity) (hpositive x u v huv)

end
end PositiveEinsteinFour.Geometry
end


section

/-! Strict positivity of the Einstein constant from the concrete sectional
curvature predicate. No Ricci-positivity hypothesis is retained. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M} {c : M}

theorem coordinateVector_pair_independent {i j : Fin 4} (hij : i ≠ j) :
    LinearIndependent ℝ ![coordinateVector i, coordinateVector j] := by
  apply linearIndependent_fin2.mpr
  constructor
  · intro hz
    have hv := congrArg (fun v : FourSpace => v j) hz
    simp [coordinateVector] at hv
  · intro a he
    have hv := congrArg (fun v : FourSpace => v i) he
    simp [coordinateVector, hij] at hv

theorem frameCurvature_plane_pos (e : OrthonormalFrame g c)
    (hpositive : HasPositiveSectionalCurvature g) {i j : Fin 4} (hij : i ≠ j) :
    0 < frameCurvature g c e i j j i := by
  rw [frameCurvature_sectional]
  simpa only [e.map_coordinateVector] using
    e.sectional_pos hpositive (coordinateVector i) (coordinateVector j)
      (coordinateVector_pair_independent hij)

theorem OrthonormalFrame.ricci_eq_scalar (e : OrthonormalFrame g c) (lam : ℝ)
    (h : chartRicci g c = lam • chartMetric g c) : e.ricci = lam • (1 : Mat4) := by
  unfold OrthonormalFrame.ricci
  rw [h, mul_smul_comm, smul_mul_assoc, e.orthonormal]

theorem einstein_constant_positive [Nonempty M] {lam : ℝ}
    (hEinstein : ∀ (x : M) (i j : Fin 4),
      ricciInChart g x (chartAt FourSpace x x) i j =
        lam * metricInChart g x (chartAt FourSpace x x) i j)
    (hpositive : HasPositiveSectionalCurvature g) : 0 < lam := by
  let x : M := Classical.choice inferInstance
  let e : OrthonormalFrame g x := canonicalFrame g x
  have hR : chartRicci g x = lam • chartMetric g x := by
    ext i j
    exact hEinstein x i j
  have hsum : 0 < ∑ i, frameCurvature g x e i 0 0 i := by
    apply Finset.sum_pos'
    · intro i _
      by_cases hi : i = 0
      · subst i
        rw [frameCurvature_first_self]
      · exact (frameCurvature_plane_pos e hpositive hi).le
    · exact ⟨1, Finset.mem_univ _, frameCurvature_plane_pos e hpositive (by decide)⟩
  rw [frameCurvature_ricci, e.ricci_eq_scalar lam hR] at hsum
  simpa using hsum

/-- The exact published positivity input is discharged for the Einstein
metrics to which the classification proof applies. -/
theorem positiveRicciInput_of_einstein [Nonempty M] (hEinstein : IsEinstein g) :
    PetersenPositiveRicciInput g := by
  obtain ⟨lam, hlam⟩ := hEinstein
  intro hpositive x
  have hp := einstein_constant_positive hlam hpositive
  have hx := hlam x 0 0
  change 0 < ricciInChart g x (chartAt FourSpace x x) 0 0
  rw [hx]
  exact mul_pos hp (chartMetric_posDef g x).diag_pos

end
end PositiveEinsteinFour.Geometry
end


section

/-! Positive constant multiplication of an actual smooth Riemannian metric.
The constructor and chart-tensor identities discharge the local part of the
classical scaling input. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bornology
open scoped Manifold ContDiff BigOperators

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem partialDeriv_const_mul (c : ℝ) (f : FourSpace → ℝ) (i : Fin 4) (z : FourSpace) :
    partialDeriv (fun w => c * f w) i z = c * partialDeriv f i z := by
  change fderiv ℝ (c • f) z (coordinateVector i) = _
  rw [fderiv_const_smul_field]
  rfl

theorem matrix_inv_const_smul (A : Mat4) (c : ℝ) (hc : c ≠ 0) :
    (c • A)⁻¹ = c⁻¹ • A⁻¹ := by
  by_cases hA : A.det = 0
  · have hscaled : (c • A).det = 0 := by rw [Matrix.det_smul, hA, mul_zero]
    rw [Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hscaled]),
      Matrix.nonsing_inv_apply_not_isUnit _ (by simp [hA]), smul_zero]
  · simpa [Units.smul_def] using Matrix.inv_smul' A (Units.mk0 c hc) (isUnit_iff_ne_zero.mpr hA)

private theorem inverse_scale_product (c a b d e : ℝ) (hc : c ≠ 0) :
    (c⁻¹ * a) * (c * b + c * d - c * e) = a * (b + d - e) := by
  field_simp [hc]

theorem christoffel_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) (z : FourSpace) (k i j : Fin 4) :
    christoffel (rescaleMetric g c hc) x z k i j = christoffel g x z k i j := by
  simp only [christoffel, metricInChart_rescaleMetric,
    matrix_inv_const_smul _ _ hc.ne', Matrix.smul_apply, smul_eq_mul,
    partialDeriv_const_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro l _
  exact inverse_scale_product c _ _ _ _ hc.ne'

theorem curvatureComponent_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) (z : FourSpace) (l i j k : Fin 4) :
    curvatureComponent (rescaleMetric g c hc) x z l i j k =
      curvatureComponent g x z l i j k := by
  simp only [curvatureComponent, christoffel_rescaleMetric]

theorem chartRicci_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) : chartRicci (rescaleMetric g c hc) x = chartRicci g x := by
  ext i j
  simp only [chartRicci, ricciInChart, curvatureComponent_rescaleMetric]

theorem sectionalNumerator_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) (z : FourSpace) (u v : FourSpace) :
    sectionalNumerator (rescaleMetric g c hc) x z u v =
      c * sectionalNumerator g x z u v := by
  simp only [sectionalNumerator, metricInChart_rescaleMetric,
    curvatureComponent_rescaleMetric, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum, mul_assoc]

end
end PositiveEinsteinFour.Geometry
end


section

/-! Constant scaling of the actual path metric. The proof uses the defining
infimum over smooth paths, including the case where no such path exists. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem metricTangentNorm_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) (v : TangentSpace I4 x) :
    metricTangentNorm (rescaleMetric g c hc) x v =
      Real.sqrt c * metricTangentNorm g x v := by
  rw [metricTangentNorm_eq_sqrt, metricTangentNorm_eq_sqrt, rescaleMetric_inner,
    Real.sqrt_mul hc.le]

theorem metricTangentENorm_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x : M) (v : TangentSpace I4 x) :
    metricTangentENorm (rescaleMetric g c hc) x v =
      ENNReal.ofReal (Real.sqrt c) * metricTangentENorm g x v := by
  rw [metricTangentENorm_eq_ofReal, metricTangentENorm_eq_ofReal,
    metricTangentNorm_rescaleMetric, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

theorem metricEDistance_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x y : M) :
    metricEDistance (rescaleMetric g c hc) x y =
      ENNReal.ofReal (Real.sqrt c) * metricEDistance g x y := by
  have hzero : ENNReal.ofReal (Real.sqrt c) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc))
  simp only [metricEDistance_eq_iInf, metricTangentENorm_rescaleMetric,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ENNReal.mul_iInf_of_ne hzero ENNReal.ofReal_ne_top]

theorem scaledEDistance_rescaleMetric (g : SmoothMetric M) (c : ℝ) (hc : 0 < c)
    (x y : M) :
    scaledEDistance (rescaleMetric g c hc) 1 x y = scaledEDistance g c x y := by
  change ENNReal.ofReal (Real.sqrt 1) * metricEDistance (rescaleMetric g c hc) x y =
    ENNReal.ofReal (Real.sqrt c) * metricEDistance g x y
  simpa only [Real.sqrt_one, ENNReal.ofReal_one, one_mul] using
    metricEDistance_rescaleMetric g c hc x y

end
end PositiveEinsteinFour.Geometry
end


section

/-! A positive scalar change of metric transports the actual clopen
orientation of the orthonormal frame bundle. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Matrix
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

theorem petersenScalingInput (g : SmoothMetric M) : PetersenScalingInput g := by
  intro c hc
  refine ⟨rescaleMetric g c hc, chartMetric_rescaleMetric g c hc,
    chartRicci_rescaleMetric g c hc, ?_, scaledEDistance_rescaleMetric g c hc, ?_⟩
  · intro x u v
    exact sectionalNumerator_rescaleMetric g c hc x _ u v
  · intro o
    exact ⟨rescaleFrameOrientation g c hc o⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry04
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.ScalarPartition.instFintypeι _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.scalarBaseSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicNegative_finite _root_.OAI.PositiveEinsteinFour.Geometry.smoothHarmonicPositive_finite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSpectralSpaceFinite _root_.OAI.PositiveEinsteinFour.Geometry.twoFormWeitzenbockKernel_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The regularized Weyl cube root is an actual smooth base scalar.
Its moments and Dirichlet energy agree with the frame quantities in the
regularized gap argument. The sharp scalar inequality remains explicit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.weylScalarFrameCompact
/-- Actual smooth scalar Sobolev suffices for the Weyl gap. No special
Sobolev premise on frame fields or their derivatives is needed. -/
theorem plus_gap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hsharp : SharpScalarSobolev o (canonicalParallelMetricData g o hRic))
    (hnonzero : ∃ x, plusNorm o x ≠ 0) :
    1 ≤ ∫ x, plusNorm o x ^ 2 ∂normalizedVolume g := by
  apply plus_gap_of_regularized_sharp_sobolev g o
    (canonicalParallelMetricData g o hRic).toMetricGreenData
  · exact sharpScalarSobolev_regularized o (canonicalParallelMetricData g o hRic)
      (canonicalParallelMetricData_orientation o hRic) hsharp
  · exact hnonzero

end
end PositiveEinsteinFour.Geometry
end


section

/-! Reversing the actual frame orientation exchanges the two Weyl norms.
The plus-block Sobolev argument therefore proves both norm gaps, without
assuming reflection preservation of a fixed oriented frame measure. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory Set
open scoped BigOperators Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] {g : SmoothMetric M}

theorem plusNorm_reversed (o : FrameOrientation g) (x : M) :
    plusNorm o.reversed x = minusNorm o x := by
  let e := o.reversed.frame x
  have hp : (⟨x, e.reflect⟩ : FrameBundle g) ∈ o.positive := o.reversed.frame_positive x
  have he := actual_minusNorm_frame o (⟨x, e.reflect⟩ : FrameBundle g) hp
  change minusNorm o x = normalizedBlockNorm (minusWeyl g x e.reflect) at he
  rw [minusWeyl_reflect] at he
  exact he.symm

variable [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M]

local instance oppositeGap_frameCompact_rdb049b_1 : CompactSpace (FrameBundle g) :=
  actual_compactFrameBundle g
/-- The same sharp scalar inequality, used with the opposite orientation,
gives the minus-block gap. -/
theorem minus_gap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hsharp : SharpScalarSobolev o.reversed (canonicalParallelMetricData g o.reversed hRic))
    (hnonzero : ∃ x, minusNorm o x ≠ 0) :
    1 ≤ ∫ x, minusNorm o x ^ 2 ∂normalizedVolume g := by
  have hn : ∃ x, plusNorm o.reversed x ≠ 0 := by
    simpa only [plusNorm_reversed] using hnonzero
  simpa only [plusNorm_reversed] using
    plus_gap_of_sharpScalarSobolev o.reversed hRic hsharp hn

/-- Both scalar Sobolev instances suffice for the original geometric gap
input. The sharp scalar premise remains explicit. -/
theorem gurskyLeBrunGap_of_sharpScalarSobolev (o : FrameOrientation g) (hRic : RicciThree g)
    (hplus : SharpScalarSobolev o (canonicalParallelMetricData g o hRic))
    (hminus : SharpScalarSobolev o.reversed (canonicalParallelMetricData g o.reversed hRic)) :
    GurskyLeBrunGapInput g o :=
  ⟨plus_gap_of_sharpScalarSobolev o hRic hplus,
    minus_gap_of_sharpScalarSobolev o hRic hminus⟩

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_HodgeTheory08
attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.oneFormC0_complete _root_.OAI.PositiveEinsteinFour.Geometry.oneFormCoexactSpectralFinite _root_.OAI.PositiveEinsteinFour.Geometry.oneFormEigenIndex_countable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormEigenIndexCountable _root_.OAI.PositiveEinsteinFour.Geometry.twoFormSmoothEigenFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The sharp scalar Sobolev inequality and the two Weyl gaps follow from
actual variational minima, their proved positive smooth regularity, Euler
rigidity and the critical exponent limit. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour MeasureTheory
open scoped Manifold ContDiff ENNReal

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M] [Nonempty M]
  [MeasurableSpace M] [BorelSpace M] [PreconnectedSpace M]

attribute [local instance] OAI.PositiveEinsteinFour.Geometry.sharpScalar_frameCompact
theorem actual_gurskyLeBrunGap (g : SmoothMetric M) (o : FrameOrientation g)
    (hRic : RicciThree g) : GurskyLeBrunGapInput g o :=
  gurskyLeBrunGap_of_sharpScalarSobolev o hRic
    (actual_sharpScalarSobolev g o hRic (canonicalParallelMetricData g o hRic))
    (actual_sharpScalarSobolev g o.reversed hRic
      (canonicalParallelMetricData g o.reversed hRic))

end
end PositiveEinsteinFour.Geometry
end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_CurvatureTensors11
attribute [-simp] _root_.OAI.PositiveEinsteinFour.Geometry.roundPolarPoint_tail _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_first _root_.OAI.PositiveEinsteinFour.Geometry.roundSphereLinearInclusion_tail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! The balanced moment argument from the actual index integrals. The same
positive measure factor occurs in the volume bound and both index formulas,
so its numerical value is not needed. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  {g : SmoothMetric M} {orientation : FrameOrientation g}

theorem MetricGreenData.canonical_balanced_moments
    (d : MetricGreenData g (canonicalFrameMeasure g orientation))
    (op : OppositeWeylData d) (hRic : RicciThree g)
    (hpositive : HasPositiveSectionalCurvature g)
    (hpinch : ∀ e, d.plusNormField e + d.minusNormField op e < 2)
    (hp : ∃ e ∈ orientation.positive, d.plusNormField e ≠ 0)
    (hm : ∃ e ∈ orientation.positive, d.minusNormField op e ≠ 0)
    (hvp : (∫ e, MomentObstruction.H (d.plusNormField e) ^ 2
          ∂canonicalFrameMeasure g orientation) -
        (∫ e, MomentObstruction.H (d.plusNormField e)
          ∂canonicalFrameMeasure g orientation) ^ 2 ≤
      (9 / 16 : ℝ) * ((∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation) -
        ∫ e, d.plusNormField e ∂canonicalFrameMeasure g orientation))
    (hvm : (∫ e, MomentObstruction.H (d.minusNormField op e) ^ 2
          ∂canonicalFrameMeasure g orientation) -
        (∫ e, MomentObstruction.H (d.minusNormField op e)
          ∂canonicalFrameMeasure g orientation) ^ 2 ≤
      (9 / 16 : ℝ) * ((∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation) -
        ∫ e, d.minusNormField op e ∂canonicalFrameMeasure g orientation)) :
    (∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation) =
      ∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation := by
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hi {f : FrameBundle g → ℝ} (hf : Continuous f) :
      Integrable f (canonicalFrameMeasure g orientation) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hn := (actual_orientedNormRegularity orientation).toPetersenInput
  have hvol := actual_finitePositiveVolume g
  have hib := orientedNormSquares_integrable orientation hn hvol
  have hframe := norm_square_frame_integrals
    (canonicalFrameMeasure_energy g orientation).averaging Angular.actual_follandMoments hn
    (canonicalFrameMeasure_supported g orientation)
    (hi (d.plusNormField.continuous.pow 2))
    (hi ((d.minusNormField op).continuous.pow 2)) hib.1 hib.2
  change ((∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation) = _) ∧
    ((∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation) = _) at hframe
  have hupper := normalized_volume_ratio_upper g orientation hRic hpositive
  rw [integral_add hib.1 hib.2, ← hframe.1, ← hframe.2] at hupper
  obtain ⟨n, m, heuler, hsignature⟩ := normalized_hodge_counts g orientation hRic
  rw [← hframe.1, ← hframe.2] at heuler hsignature
  have hgap := actual_gurskyLeBrunGap g orientation hRic
  have hplusgap : 1 ≤ ∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation := by
    obtain ⟨e, he, hne⟩ := hp
    have he' : plusNorm orientation e.base ≠ 0 := by
      rw [hn.plusFrame e he]
      exact hne
    rw [hframe.1]
    exact hgap.1 ⟨e.base, he'⟩
  have hminusgap : 1 ≤ ∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation := by
    obtain ⟨e, he, hne⟩ := hm
    have he' : minusNorm orientation e.base ≠ 0 := by
      rw [hn.minusFrame e he]
      exact hne
    rw [hframe.2]
    exact hgap.2 ⟨e.base, he'⟩
  have hpb (e : FrameBundle g) : d.plusNormField e ∈ Set.Icc (0 : ℝ) 2 := by
    refine ⟨normalizedBlockNorm_nonneg _, ?_⟩
    have hb : 0 ≤ d.minusNormField op e := normalizedBlockNorm_nonneg _
    linarith only [hpinch e, hb]
  have hmb (e : FrameBundle g) : d.minusNormField op e ∈ Set.Icc (0 : ℝ) 2 := by
    refine ⟨normalizedBlockNorm_nonneg _, ?_⟩
    have hv : 0 ≤ d.plusNormField e := normalizedBlockNorm_nonneg _
    linarith only [hpinch e, hv]
  have hHplus : Continuous (fun e => MomentObstruction.H (d.plusNormField e) ^ 2) := by
    unfold MomentObstruction.H
    fun_prop
  have hHminus : Continuous (fun e => MomentObstruction.H (d.minusNormField op e) ^ 2) := by
    unfold MomentObstruction.H
    fun_prop
  exact (balanced_moments n m (2 * (volumeRatio g / riemannianChartFactor.toReal))
    d.plusNormField.continuous.aestronglyMeasurable
    (d.minusNormField op).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall hpb) (Filter.Eventually.of_forall hmb)
    (Filter.Eventually.of_forall fun e => (hpinch e).le)
    (hi d.plusNormField.continuous) (hi (d.minusNormField op).continuous)
    (hi (d.plusNormField.continuous.pow 2)) (hi ((d.minusNormField op).continuous.pow 2))
    (hi hHplus) (hi hHminus) hplusgap hminusgap
    (frame_norm_moment_sum_lt_four d op hpinch)
    (mul_pos (by norm_num) (div_pos (volumeRatio_pos hvol) riemannianChartFactor_toReal_pos))
    (by linarith only [hupper]) heuler (by nlinarith only [hsignature]) hvp hvm).1

end
end PositiveEinsteinFour.Geometry
end


section

/-! The actual oriented metric has one vanishing Weyl block. Euler and
signature enter through the proved heat-index integrals, not a published
Hodge assumption. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour TraceHessian MeasureTheory
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem actual_one_weyl_block_zero (g : SmoothMetric M) (orientation : FrameOrientation g)
    (hRic : RicciThree g) (hpositive : HasPositiveSectionalCurvature g) :
    (∀ c, plusWeyl g c (orientation.frame c) = 0) ∨
      ∀ c, minusWeyl g c (orientation.frame c) = 0 := by
  let p := canonicalParallelMetricData g orientation hRic
  let d := p.toMetricGreenData
  have hparallel : ParallelReflection d := actualParallelMetricData_reflection g
    (canonicalFrameMeasure g orientation)
    (parallelFrameFlowMap_measurePreserving g orientation) hRic
  let op := d.oppositeData hparallel hRic
  let : CompactSpace (FrameBundle g) := actual_compactFrameBundle g
  have hn := (actual_orientedNormRegularity orientation).toPetersenInput
  have hp := shiftedCurvaturePositive_of_published (actual_sectionalInput g) hRic hpositive
  have hpinch := strict_norm_pinching_of_published d op (actual_sectionalInput g) hRic hpositive
  have hdecomp (e : FrameBundle g) : frameCurvature g e.base e.frame =
      Angular.einsteinCurvatureTensor (plusWeyl g e.base e.frame) (minusWeyl g e.base e.frame) :=
    actual_einstein_decomposition e.frame hRic
  let s : ScalarVarianceInputs d orientation := {
    norms := hn
    orientationFlow := canonicalParallelMetricData_orientation orientation hRic
    supported := canonicalFrameMeasure_supported g orientation
    calculus := p.scalarCalculus.toPetersenInput
    poisson := actual_petersen_poisson g orientation hRic
    positive := hp
    decomposition := hdecomp }
  have hi {f : FrameBundle g → ℝ} (hf : Continuous f) :
      Integrable f (canonicalFrameMeasure g orientation) :=
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hib := orientedNormSquares_integrable orientation hn (actual_finitePositiveVolume g)
  have hframe := norm_square_frame_integrals
    (canonicalFrameMeasure_energy g orientation).averaging Angular.actual_follandMoments hn
    (canonicalFrameMeasure_supported g orientation)
    (hi (d.plusNormField.continuous.pow 2))
    (hi ((d.minusNormField op).continuous.pow 2)) hib.1 hib.2
  change ((∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation) = _) ∧
    ((∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation) = _) at hframe
  have hgap := actual_gurskyLeBrunGap g orientation hRic
  have hpgap : (∃ e ∈ orientation.positive, d.plusNormField e ≠ 0) →
      1 ≤ ∫ e, d.plusNormField e ^ 2 ∂canonicalFrameMeasure g orientation := by
    rintro ⟨e, he, hne⟩
    have he' : plusNorm orientation e.base ≠ 0 := by
      rw [hn.plusFrame e he]
      exact hne
    rw [hframe.1]
    exact hgap.1 ⟨e.base, he'⟩
  have hmgap : (∃ e ∈ orientation.positive, d.minusNormField op e ≠ 0) →
      1 ≤ ∫ e, d.minusNormField op e ^ 2 ∂canonicalFrameMeasure g orientation := by
    rintro ⟨e, he, hne⟩
    have he' : minusNorm orientation e.base ≠ 0 := by
      rw [hn.minusFrame e he]
      exact hne
    rw [hframe.2]
    exact hgap.2 ⟨e.base, he'⟩
  have hz : (∀ e ∈ orientation.positive, d.plusNormField e = 0) ∨
      ∀ e ∈ orientation.positive, d.minusNormField op e = 0 := by
    classical
    by_cases hv : ∀ e ∈ orientation.positive, d.plusNormField e = 0
    · exact Or.inl hv
    by_cases hb : ∀ e ∈ orientation.positive, d.minusNormField op e = 0
    · exact Or.inr hb
    push Not at hv hb
    have hsecond := d.canonical_balanced_moments op hRic hpositive hpinch hv hb
      (d.plusHVariance op s hparallel hpinch) (d.minusHVariance op s hparallel hpinch)
    exact d.one_block_zero_of_variance op orientation hparallel hp hdecomp hpinch hsecond
      (d.normDifferenceVariance op s hparallel hpinch)
      (d.plusNormVariance op s hparallel hpinch) (d.minusNormVariance op s hparallel hpinch)
      hpgap hmgap
  rcases hz with hz | hz
  · exact Or.inl (fun c => (plusNorm_eq_zero_iff orientation c).mp (by
      rw [hn.plusFrame ⟨c, orientation.frame c⟩ (orientation.frame_positive c)]
      exact hz ⟨c, orientation.frame c⟩ (orientation.frame_positive c)))
  · exact Or.inr (fun c => (minusNorm_eq_zero_iff orientation c).mp (by
      rw [hn.minusFrame ⟨c, orientation.frame c⟩ (orientation.frame_positive c)]
      exact hz ⟨c, orientation.frame c⟩ (orientation.frame_positive c)))

end
end PositiveEinsteinFour.Geometry
end

end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_GeodesicGeometry12
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


section

/-! Exact classification with only the published half-conformally-flat
model identification left explicit. The Hodge/index, analytic and covering
inputs are all supplied by their actual proofs. -/
namespace PositiveEinsteinFour.Geometry
open EinsteinFour
open scoped Manifold ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M] [T3Space M] [CompactSpace M]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem models_of_actual_normalized_model_input (g : SmoothMetric M)
    (o : FrameOrientation g) (hRic : RicciThree g)
    (hmodel : DerdzinskiHitchinInput g o)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance) :=
  hmodel inferInstance inferInstance inferInstance inferInstance hEinstein hpositive
    (actual_one_weyl_block_zero g o hRic hpositive)

theorem models_of_actual_model_inputs (g : SmoothMetric M) (orientation : FrameOrientation g)
    (hmodel : ∀ (h : SmoothMetric M) (o : FrameOrientation h),
      RicciThree h → DerdzinskiHitchinInput h o)
    (hEinstein : IsEinstein g) (hpositive : HasPositiveSectionalCurvature g) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo g a roundDistance ∨
      ScaledIsometricTo g a fubiniStudyDistance) := by
  obtain ⟨h, o, c, hc, hRic, hp, hd⟩ := normalized_oriented_metric g orientation
    (positiveRicciInput_of_einstein hEinstein) (petersenScalingInput g) hEinstein hpositive
  obtain ⟨a, ha, hmodels⟩ := models_of_actual_normalized_model_input h o hRic
    (hmodel h o hRic) (einstein_of_ricciThree hRic) hp
  have hscale (x y : M) : scaledEDistance h a x y = scaledEDistance g (a * c) x y := by
    calc
      _ = scaledEDistance h (a * 1) x y := by rw [mul_one]
      _ = ENNReal.ofReal (Real.sqrt a) * scaledEDistance h 1 x y :=
        scaledEDistance_mul h a 1 ha.le x y
      _ = ENNReal.ofReal (Real.sqrt a) * scaledEDistance g c x y := by rw [hd]
      _ = _ := (scaledEDistance_mul g a c ha.le x y).symm
  refine ⟨a * c, mul_pos ha hc, ?_⟩
  rcases hmodels with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl ⟨f, fun x y => (hf x y).trans (hscale x y)⟩
  · exact Or.inr ⟨f, fun x y => (hf x y).trans (hscale x y)⟩

end
end PositiveEinsteinFour.Geometry

end


end OAI
end

section
-- module Solutions.OAIQ091_EF.EinsteinFour_ActualModelIdentification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual half-conformally-flat model identification. All analytic,
index, injectivity, and metric-model inputs are supplied by proved geometry. -/

namespace PositiveEinsteinFour
open EinsteinFour _root_.OAI.PositiveEinsteinFour.Geometry
open scoped Manifold ContDiff
noncomputable section
universe u

/-- Every connected closed oriented positively curved Einstein four-manifold is,
up to positive scaling and isometry, the round S4 or Fubini–Study CP2. -/
theorem orientedClassification_oai (X : ClosedOrientedMetricFour.{u})
    (hEinstein : IsEinstein X.metric) (hpositive : HasPositiveSectionalCurvature X.metric) :
    ∃ a : ℝ, 0 < a ∧ (ScaledIsometricTo X.metric a roundDistance ∨
      ScaledIsometricTo X.metric a fubiniStudyDistance) := by
  let : MeasurableSpace X.manifold := borel X.manifold
  let : BorelSpace X.manifold := ⟨rfl⟩
  exact models_of_actual_model_inputs X.metric X.orientation
    actual_derdzinski_hitchin hEinstein hpositive

end
end PositiveEinsteinFour

end OAI
end

theorem solution.{u} : type_of% @OAI.PositiveEinsteinFour.orientedClassification_oai.{u} := @OAI.PositiveEinsteinFour.orientedClassification_oai.{u}
