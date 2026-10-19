-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness.orthogonalBranch_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/28d57f1a-4f29-4726-9ec5-27b427fa4449

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
noncomputable section
set_option autoImplicit false
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
theorem _root_.solution
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (i : ι) (x : V) :
    x ∈ LinearMap.range (f i).toLinearMap ↔
      ∀ j : ι, j ≠ i → ∀ y : E j, ⟪x, f j y⟫_ℝ = 0 := by
  classical
  constructor
  · rintro ⟨p, rfl⟩ j hji y
    exact horth i j (Ne.symm hji) p y
  · intro hx
    have hzero : ∀ j : ι, j ≠ i →
        (LinearMap.range (f j).toLinearMap).starProjection x = 0 := by
      intro j hji
      apply (Submodule.starProjection_apply_eq_zero_iff
        (LinearMap.range (f j).toLinearMap)).mpr
      apply ((LinearMap.range (f j).toLinearMap).mem_orthogonal' x).mpr
      rintro _ ⟨y, rfl⟩
      exact hx j hji y
    have hsum := orthogonalBranch_sum_projection f horth hdim x
    have hsingle :
        (∑ j : ι,
          (LinearMap.range (f j).toLinearMap).starProjection x) =
          (LinearMap.range (f i).toLinearMap).starProjection x := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact hzero j hji
      · simp
    rw [hsingle] at hsum
    rw [← hsum]
    exact Submodule.starProjection_apply_mem _ x
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
