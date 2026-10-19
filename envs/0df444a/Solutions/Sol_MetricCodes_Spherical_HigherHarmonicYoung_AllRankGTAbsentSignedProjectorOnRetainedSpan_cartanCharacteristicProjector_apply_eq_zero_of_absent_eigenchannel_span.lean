-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan.cartanCharacteristicProjector_apply_eq_zero_of_absent_eigenchannel_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/14e8af64-89db-47f7-a996-e7f4dcc3548e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankCartanCharacteristicInterpolation_cartanCharacteristicInterpolationProjector_apply_of_eigenvector

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
    {κ ι V : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    [AddCommGroup V] [Module ℝ V]
    {E : ι → Type*} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (nodes : κ → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V) (selected : κ)
    (channelIndex : ι → κ)
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (heigen : ∀ (i : ι) (p : E i),
      T (A i p) = nodes (channelIndex i) • A i p)
    (habsent : ∀ i : ι, selected ≠ channelIndex i)
    (x : V) (hx : x ∈ (⨆ i : ι, LinearMap.range (A i))) :
    cartanCharacteristicInterpolationProjector nodes T selected x = 0 := by
  let P := cartanCharacteristicInterpolationProjector nodes T selected
  have hle : (⨆ i : ι, LinearMap.range (A i)) ≤ LinearMap.ker P := by
    apply iSup_le
    intro i
    rintro _ ⟨p, rfl⟩
    change P (A i p) = 0
    dsimp [P]
    rw [cartanCharacteristicInterpolationProjector_apply_of_eigenvector
      nodes T hnode selected (channelIndex i) (A i p) (heigen i p),
      if_neg (habsent i)]
  exact hle hx
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTAbsentSignedProjectorOnRetainedSpan
