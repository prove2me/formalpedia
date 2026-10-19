-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality.youngClebschLower_adjoint_signedEigen_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/4fa24f2e-6c3e-4f69-a8f6-47abdbf92e2b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicInterpolation_signedAmbientCharacteristicNodes_injective
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirProjector_gtRelativeCasimir_raise_channel
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTRelativeCasimirCompressedResolvent_gtRelativeCasimir_eigen_inner_eq_zero

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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCartanHodgeSelector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTCompressedResolventSpectral
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirCompressedResolvent
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRowMickelssonWeightHomogeneity
open MetricCodes.Spherical.HigherRepresentationGraph
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
theorem _root_.solution
    {r n : ℕ} (low : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n low mu)
    (row : Fin (r + 1)) (channel : Fin (r + 1) × Bool)
    (hne : channel ≠ (row, true))
    (v : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) low)
    (hv : gtRelativeCasimir low v =
      signedNode (HigherChannel.ambientShift n low) channel • v) :
    (youngClebschLower low (raiseWeight low row)
      (sum_raiseWeight low row) row).adjoint v = 0 := by
  apply ext_inner_left ℝ
  intro p
  rw [LinearMap.adjoint_inner_right, inner_zero_right]
  apply gtRelativeCasimir_eigen_inner_eq_zero low
    (youngClebschLower low (raiseWeight low row)
      (sum_raiseWeight low row) row p) v
    (signedNode (HigherChannel.ambientShift n low) (row, true))
    (signedNode (HigherChannel.ambientShift n low) channel)
  · exact gtRelativeCasimir_raise_channel low row
      (youngClebschLower low (raiseWeight low row)
        (sum_raiseWeight low row) row)
      (fun a b => ClebschRotation.youngClebschLower_rotation_intertwine
        low (raiseWeight low row) (sum_raiseWeight low row) row a b) p
  · exact hv
  · intro heq
    apply hne
    exact (signedAmbientCharacteristicNodes_injective hfinite heq).symm
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTSelectedRestrictedProjectorEquality
