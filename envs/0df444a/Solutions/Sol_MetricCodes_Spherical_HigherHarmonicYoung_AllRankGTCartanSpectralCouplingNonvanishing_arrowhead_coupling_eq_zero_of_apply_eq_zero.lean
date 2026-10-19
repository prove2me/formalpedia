-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing.arrowhead_coupling_eq_zero_of_apply_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/c8a81cb5-eb61-48b1-ae53-f1a40ca15ddb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseCouplingNonzero_polynomial_eigenvector_eq_zero_of_annihilating_eval_ne_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCartanSpectralCouplingNonvanishing_arrowhead_eigen_of_coupling_kernel
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallTransverseCompression.gtTransverseWallTensorEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_toLinearMap
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTWallSectorIsometry.normalizedGTTransverseWallSector_apply
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition.gtFullTransverseInternalEmbedding_tmul
attribute [local simp] MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition.gtFullAxisEmbedding_apply

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAmbientCharacteristicAtTransverseNode
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseCouplingNonzero
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
theorem _root_.solution
    {E F V : Type*}
    [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F]
    [AddCommGroup V] [Module ℝ V]
    (T : Module.End ℝ V)
    (B : E →ₗ[ℝ] V) (hB : Function.Injective B)
    (A : F →ₗ[ℝ] V) (K : E →ₗ[ℝ] F)
    (P : Polynomial ℝ) (d : ℝ)
    (hrow : T.comp B = d • B + A.comp K)
    (hchar : ∀ p : E, Polynomial.aeval T P (B p) = 0)
    (heval : P.eval d ≠ 0)
    (p : E) (hp : K p = 0) : p = 0 := by
  have heigen := arrowhead_eigen_of_coupling_kernel
    T B A K d hrow p hp
  have hzero := polynomial_eigenvector_eq_zero_of_annihilating_eval_ne_zero
    T P d (B p) heigen (hchar p) heval
  exact hB (by simpa using hzero)
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanSpectralCouplingNonvanishing
