-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness.actualTensorClebsch_iSup_range_eq_top_of_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:45.453197+00:00
-- url     : https://prove2.me/submissions/5b8bc27c-cc90-4e04-8575-3d8bed843ee4

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankOrthogonalBranchCompleteness_orthogonalBranch_iSup_range_eq_top

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
    {ι : Type*} [Fintype ι]
    {r n : ℕ} (hn : 2 * r + 2 ≤ n)
    (target : Fin (r + 1) → ℕ) (hdom : Antitone target)
    (source : ι → Fin (r + 1) → ℕ)
    (hsource : ∀ i, IsAllRankOneBoxNeighbor target (source i))
    (hinj : Function.Injective source)
    (A : (i : ι) → HarmonicYoungSpace (n := n) (source i) →ₗᵢ[ℝ]
      (SpherePacking.Euclidean n ⊗[ℝ]
        HarmonicYoungSpace (n := n) target))
    (hA : ∀ (i : ι) (a b : Fin n),
      (A i).toLinearMap.comp (youngAmbientRotation (source i) a b) =
        (ClebschRotation.tensorAmbientRotation target a b).comp
          (A i).toLinearMap)
    (hdim : n * Module.finrank ℝ (HarmonicYoungSpace (n := n) target) =
      ∑ i : ι, Module.finrank ℝ
        (HarmonicYoungSpace (n := n) (source i))) :
    (⨆ i : ι, LinearMap.range (A i).toLinearMap) =
      (⊤ : Submodule ℝ
        (SpherePacking.Euclidean n ⊗[ℝ]
          HarmonicYoungSpace (n := n) target)) := by
  apply orthogonalBranch_iSup_range_eq_top A
  · intro i j hij p q
    have hne : source i ≠ source j := fun h => hij (hinj h)
    have hzero := allRankYoungChannel_crossGram_eq_zero_of_oneBoxNeighbors
      hn target (source i) (source j) hdom (hsource i) (hsource j) hne
      (A i).toLinearMap (A j).toLinearMap (hA i) (hA j)
    calc
      ⟪A i p, A j q⟫_ℝ =
          ⟪p, (A i).toLinearMap.adjoint (A j q)⟫_ℝ :=
            (LinearMap.adjoint_inner_right (A i).toLinearMap p (A j q)).symm
      _ = 0 := by
        have hz : (A i).toLinearMap.adjoint (A j q) = 0 := by
          simpa using LinearMap.congr_fun hzero q
        rw [hz]
        exact @inner_zero_right ℝ
          (HarmonicYoungSpace (n := n) (source i)) _ _ _ p
  · rw [Module.finrank_tensorProduct]
    simpa [SpherePacking.Euclidean] using hdim
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschCompleteness
