-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness.orthogonalBranchSum_range
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.102863+00:00
-- url     : https://prove2.me/submissions/b53b6c9b-5089-42ce-8b9e-7682bbd2506c

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
    (f : (i : ι) → E i →ₗᵢ[ℝ] V) :
    LinearMap.range (orthogonalBranchSum f) =
      ⨆ i, LinearMap.range (f i).toLinearMap := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [orthogonalBranchSum_apply]
    apply Submodule.sum_mem
    intro i _
    exact (le_iSup
      (fun j => LinearMap.range (f j).toLinearMap) i)
      ⟨x i, rfl⟩
  · apply iSup_le
    intro i
    rintro _ ⟨x, rfl⟩
    refine ⟨Pi.single i x, ?_⟩
    exact LinearMap.lsum_piSingle ℝ E ℝ
      (fun j => (f j).toLinearMap) i x
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
