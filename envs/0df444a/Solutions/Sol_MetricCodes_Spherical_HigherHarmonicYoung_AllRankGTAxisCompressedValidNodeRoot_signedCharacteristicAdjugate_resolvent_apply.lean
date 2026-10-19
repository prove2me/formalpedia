-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot.signedCharacteristicAdjugate_resolvent_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/0769caf0-3bb5-4650-ab6b-5c7b5b8021f5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCompressedResolvent_sum_signedCharacteristicProjector
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTCompressedResolvent_signedCharacteristicProjector_eigen_of_aeval_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallTransverseCompression_gtTransverseWallTensorEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_toLinearMap
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTWallSectorIsometry_normalizedGTTransverseWallSector_apply
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTTransverseFullBranchDecomposition_gtFullTransverseInternalEmbedding_tmul
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTActualAxisTransverseDecomposition_gtFullAxisEmbedding_apply
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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 700000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedCharacteristicMinor
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherRepresentationGraph (Interlaces)
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot
theorem _root_.solution
    {r : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (L : Fin (r + 1) → ℝ)
    (hL : Function.Injective (signedNode L))
    (T : Module.End ℝ V) (z : ℝ) (v : V)
    (hchar : Polynomial.aeval T (signedAmbientCharacteristic L) v = 0) :
    (z • (LinearMap.id : Module.End ℝ V) - T)
        (signedCharacteristicAdjugate L T z v) =
      (signedAmbientCharacteristic L).eval z • v := by
  classical
  unfold signedCharacteristicAdjugate
  simp only [LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, LinearMap.sum_apply]
  rw [Finset.smul_sum, map_sum, ← Finset.sum_sub_distrib]
  have hterm (channel : Fin (r + 1) × Bool) :
      z • ((Lagrange.nodal
          ((Finset.univ : Finset (Fin (r + 1) × Bool)).erase channel)
          (signedNode L)).eval z •
            signedCharacteristicProjector L T channel v) -
        T ((Lagrange.nodal
          ((Finset.univ : Finset (Fin (r + 1) × Bool)).erase channel)
          (signedNode L)).eval z •
            signedCharacteristicProjector L T channel v) =
        (signedAmbientCharacteristic L).eval z •
          signedCharacteristicProjector L T channel v := by
    rw [map_smul,
      signedCharacteristicProjector_eigen_of_aeval_apply
        L T channel v hchar,
      smul_smul, smul_smul, ← sub_smul]
    congr 1
    have hnodal := congrArg (Polynomial.eval z)
      (Lagrange.nodal_eq_mul_nodal_erase
        (s := (Finset.univ : Finset (Fin (r + 1) × Bool)))
        (v := signedNode L) (Finset.mem_univ channel))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C] at hnodal
    change
      z * _ - _ * signedNode L channel =
        (signedAmbientCharacteristic L).eval z
    change
      z * _ - _ * signedNode L channel =
        (Lagrange.nodal Finset.univ (signedNode L)).eval z
    nlinarith
  simp_rw [hterm]
  rw [← Finset.smul_sum]
  congr 1
  simpa only [LinearMap.sum_apply, LinearMap.id_apply] using
    LinearMap.congr_fun (sum_signedCharacteristicProjector L hL T) v
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAxisCompressedValidNodeRoot
