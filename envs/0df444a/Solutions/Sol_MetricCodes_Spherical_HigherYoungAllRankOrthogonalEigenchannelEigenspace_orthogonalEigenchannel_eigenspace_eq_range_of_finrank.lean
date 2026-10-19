-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankOrthogonalEigenchannelEigenspace.orthogonalEigenchannel_eigenspace_eq_range_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.872997+00:00
-- url     : https://prove2.me/submissions/b241be74-b4c8-4a98-b58c-4c1d1383d93f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalBranchCompleteness_orthogonalBranch_iSup_range_eq_top
import Theorems.Thm_MetricCodes_Spherical_HigherYoungAllRankOrthogonalEigenchannelEigenspace_orthogonalEigenchannel_eigenspace_eq_range

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
open MetricCodes.Spherical.HigherYoungAllRankOrthogonalEigenchannelEigenspace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection
namespace MetricCodes.Spherical.HigherYoungAllRankOrthogonalEigenchannelEigenspace
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (nodes : ι → ℝ) (hnode : Function.Injective nodes)
    (T : Module.End ℝ V)
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (hdim : Module.finrank ℝ V =
      ∑ i : ι, Module.finrank ℝ (E i))
    (heigen : ∀ (i : ι) (p : E i), T (A i p) = nodes i • A i p)
    (selected : ι) :
    Module.End.eigenspace T (nodes selected) =
      LinearMap.range (A selected).toLinearMap :=
  orthogonalEigenchannel_eigenspace_eq_range nodes hnode T A horth
    (orthogonalBranch_iSup_range_eq_top A horth hdim) heigen selected
end MetricCodes.Spherical.HigherYoungAllRankOrthogonalEigenchannelEigenspace
