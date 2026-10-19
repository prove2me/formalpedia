-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange.orthogonalBranch_range_eq_of_cross_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/8b794a59-71b9-4870-a464-2e8f52a49190

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalBranchCompleteness_orthogonalBranch_mem_range_of_orthogonal

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
open MetricCodes.Spherical.HigherHarmonicYoung MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGelfandTsetlinCanonicalFibre
open MetricCodes.Spherical.HigherHarmonicYoung.ArbitraryRankBranching
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherRepresentationGraph
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGTFullCrossOrthogonality
open MetricCodes.Spherical.ThreeRowYoungBranching
variable {ι : Type*} [Fintype ι]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
variable {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)]
  [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
theorem _root_.solution
    (f : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪f i p, f j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (g : F →ₗᵢ[ℝ] V) (i : ι)
    (hcross : ∀ j : ι, j ≠ i →
      ∀ p : F, ∀ q : E j, ⟪g p, f j q⟫_ℝ = 0)
    (heqdim : Module.finrank ℝ F = Module.finrank ℝ (E i)) :
    LinearMap.range g.toLinearMap =
      LinearMap.range (f i).toLinearMap := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro _ ⟨p, rfl⟩
    apply orthogonalBranch_mem_range_of_orthogonal f horth hdim i (g p)
    intro j hji q
    exact hcross j hji p q
  · calc
      Module.finrank ℝ (LinearMap.range g.toLinearMap) =
          Module.finrank ℝ F :=
        LinearMap.finrank_range_of_inj g.injective
      _ = Module.finrank ℝ (E i) := heqdim
      _ = Module.finrank ℝ (LinearMap.range (f i).toLinearMap) :=
        (LinearMap.finrank_range_of_inj (f i).injective).symm
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankCanonicalSelectedBranchRange
