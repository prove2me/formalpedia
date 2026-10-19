-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan.cartanCharacteristicProjector_apply_eq_zero_of_matching_adjoint_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/b4280027-571d-4e70-a8a9-bde7dae467a5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicInterpolation_cartanCharacteristicInterpolationProjector_apply_of_eigenvector
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankTensorClebschSpectralProjection_orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTAbsentSignedProjectorOnRetainedSpan_cartanCharacteristicProjector_apply_eq_zero_of_absent_eigenchannel_span

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
    {κ ι V : Type*} [Fintype κ] [DecidableEq κ]
    [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (nodes : κ → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V) (selected : κ)
    (channelIndex : ι → κ) (hindex : Function.Injective channelIndex)
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (heigen : ∀ (i : ι) (p : E i),
      T (A i p) = nodes (channelIndex i) • A i p)
    (x : V)
    (hx : x ∈ (⨆ i : ι, LinearMap.range (A i).toLinearMap))
    (hzero : ∀ i : ι, channelIndex i = selected →
      (A i).toLinearMap.adjoint x = 0) :
    cartanCharacteristicInterpolationProjector nodes T selected x = 0 := by
  classical
  by_cases hmatch : ∃ i : ι, channelIndex i = selected
  · obtain ⟨i, hi⟩ := hmatch
    have hselector (j : ι) (p : E j) :
        cartanCharacteristicInterpolationProjector nodes T selected (A j p) =
          if i = j then A j p else 0 := by
      rw [cartanCharacteristicInterpolationProjector_apply_of_eigenvector
        nodes T hnode selected (channelIndex j) (A j p) (heigen j p)]
      by_cases hij : i = j
      · subst j
        simp [hi]
      · have hne : selected ≠ channelIndex j := by
          intro heq
          exact hij (hindex (hi.trans heq))
        simp [hij, hne]
    rw [orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
      A horth (cartanCharacteristicInterpolationProjector nodes T selected)
      i hselector x hx, LinearMap.comp_apply, hzero i hi, map_zero]
  · apply cartanCharacteristicProjector_apply_eq_zero_of_absent_eigenchannel_span
      nodes hnode T selected channelIndex (fun i => (A i).toLinearMap)
      heigen _ x hx
    intro i h
    exact hmatch ⟨i, h.symm⟩
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
