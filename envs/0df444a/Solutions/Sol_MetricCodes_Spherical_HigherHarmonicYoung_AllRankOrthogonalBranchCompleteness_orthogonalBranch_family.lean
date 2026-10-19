-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness.orthogonalBranch_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/630f82da-e7ce-4944-a6f9-08af10324dac

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
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0) :
    OrthogonalFamily ℝ
      (fun i => LinearMap.range (f i).toLinearMap)
      (fun i => (LinearMap.range (f i).toLinearMap).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro i j hij
  apply Submodule.isOrtho_iff_inner_eq.mpr
  rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
  exact horth i j hij p q
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
