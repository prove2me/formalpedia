-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan.gtCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/5a5469ab-6d54-48ce-a257-d8be5fc9744e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_signedNode_injective
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAbsentSignedProjectorOnRetainedSpan_cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero

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
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
theorem _root_.solution
    {r n : ℕ} (target : Fin (r + 1) → ℕ)
    (mu : Fin r → ℕ) (hfinite : FiniteInterlacing n target mu)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (channelIndex : ι → Fin (r + 1) × Bool)
    (hindex : Function.Injective channelIndex)
    (A : (i : ι) → E i →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (heigen : ∀ (i : ι) (p : E i),
      gtRelativeCasimir target (A i p) =
        signedNode (ambientShift n target) (channelIndex i) • A i p)
    (selected : Fin (r + 1) × Bool)
    (x : SpherePacking.Euclidean n ⊗[ℝ]
      HarmonicYoungSpace (n := n) target)
    (hx : x ∈ (⨆ i : ι, LinearMap.range (A i).toLinearMap))
    (hzero : ∀ i : ι, channelIndex i = selected →
      (A i).toLinearMap.adjoint x = 0) :
    gtCharacteristicProjector target selected x = 0 := by
  change cartanCharacteristicInterpolationProjector
    (signedNode (ambientShift n target))
      (gtRelativeCasimir target) selected x = 0
  apply cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
    (signedNode (ambientShift n target))
    (signedNode_injective hfinite.ambientShift_pos
      hfinite.ambientShift_strictAnti.injective)
    (gtRelativeCasimir target) selected channelIndex hindex A horth heigen
    x hx hzero
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
