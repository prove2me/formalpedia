-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure.mem_submodule_of_complete_orthogonal_two_family_projections
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.631419+00:00
-- url     : https://prove2.me/submissions/6232121b-63d8-4d2b-80d8-81bb648bf5b9

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
set_option autoImplicit false
set_option maxHeartbeats 8000000
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
theorem _root_.solution
    {ι κ H : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H]
    (U : ι → Submodule ℝ H) (V : κ → Submodule ℝ H)
    (hU : ∀ i j : ι, i ≠ j → U i ⟂ U j)
    (hV : ∀ i j : κ, i ≠ j → V i ⟂ V j)
    (hUV : ∀ i : ι, ∀ j : κ, U i ⟂ V j)
    (hcomplete : (⨆ i, U i) ⊔ (⨆ j, V j) = ⊤)
    (S : Submodule ℝ H) (x : H)
    (haxis : ∀ i : ι, (U i).starProjection x ∈ S)
    (htransverse : ∀ j : κ, (V j).starProjection x ∈ S) :
    x ∈ S := by
  classical
  let W : ι ⊕ κ → Submodule ℝ H := Sum.elim U V
  have hpair : ∀ a b : ι ⊕ κ, a ≠ b → W a ⟂ W b := by
    intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact hU i j (fun hij => hab (congrArg Sum.inl hij))
      | inr j => exact hUV i j
    | inr i =>
      cases b with
      | inl j => exact (hUV j i).symm
      | inr j => exact hV i j (fun hij => hab (congrArg Sum.inr hij))
  have horth : OrthogonalFamily ℝ
      (fun i : ι ⊕ κ => ↥(W i)) (fun i => (W i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise hpair
  have hspan : (⨆ i : ι ⊕ κ, W i) = ⊤ := by
    rw [iSup_sum]
    change (⨆ i, U i) ⊔ (⨆ j, V j) = ⊤
    exact hcomplete
  have hx : x ∈ ⨆ i : ι ⊕ κ, W i := by
    rw [hspan]
    trivial
  rw [← horth.sum_projection_of_mem_iSup x hx]
  apply S.sum_mem
  intro i _
  cases i with
  | inl j => exact haxis j
  | inr j => exact htransverse j
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalSelectedTwoBlockClosure
