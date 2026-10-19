-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness.orthogonalCompleteBranch_mem_selected_iSup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/927b9f9d-66f4-435b-9409-69ac78584bd4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalBranchCompleteness_orthogonalBranch_sum_projection

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
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.MixedSignature
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
theorem _root_.solution
    {ι V : Type*} [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (P : ι → Prop) [DecidablePred P]
    (x : V)
    (hexcluded : ∀ i : ι, ¬ P i → ∀ y : E i, ⟪x, A i y⟫_ℝ = 0) :
    x ∈ (⨆ i : {i : ι // P i}, LinearMap.range (A i.val).toLinearMap) := by
  classical
  have hsum := orthogonalBranch_sum_projection A horth hdim x
  rw [← hsum]
  apply Submodule.sum_mem
  intro i _
  by_cases hi : P i
  · exact
      (le_iSup
        (fun j : {i : ι // P i} =>
          LinearMap.range (A j.val).toLinearMap)
        ⟨i, hi⟩)
          (Submodule.starProjection_apply_mem
            (LinearMap.range (A i).toLinearMap) x)
  · have hzero :
        (LinearMap.range (A i).toLinearMap).starProjection x = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff
        (LinearMap.range (A i).toLinearMap)).mpr
      apply ((LinearMap.range (A i).toLinearMap).mem_orthogonal' x).mpr
      rintro _ ⟨y, rfl⟩
      exact hexcluded i hi y
    rw [hzero]
    exact Submodule.zero_mem _
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
