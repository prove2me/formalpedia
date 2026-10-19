-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction.eq_of_iSup_range_sup_eq_top_of_adjoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/1e8ac113-aa83-4df6-a7f9-1143c4b1ae44

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalCompleteBlockReconstruction_eq_zero_of_iSup_range_sup_eq_top_of_adjoint_eq_zero

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
set_option maxHeartbeats 1600000
open scoped BigOperators InnerProductSpace TensorProduct
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
open MetricCodes.Spherical.HigherHarmonicYoung
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTActualAxisTransverseDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTRelativeCasimirProjector
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTTransverseFullBranchDecomposition
open MetricCodes.Spherical.HigherHarmonicYoung.BranchingDimension
open MetricCodes.Spherical.HigherYoungAllRankCanonicalGelfandTsetlinCompleteness
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
theorem _root_.solution
    {ι κ : Type*} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (E : ι → Type*) (F : κ → Type*)
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    [∀ j, NormedAddCommGroup (F j)]
    [∀ j, InnerProductSpace ℝ (F j)]
    [∀ j, FiniteDimensional ℝ (F j)]
    (A : (i : ι) → E i →ₗ[ℝ] V)
    (B : (j : κ) → F j →ₗ[ℝ] V)
    (hcomplete :
      (⨆ i : ι, LinearMap.range (A i)) ⊔
        (⨆ j : κ, LinearMap.range (B j)) = ⊤)
    (x y : V)
    (haxis : ∀ i : ι, (A i).adjoint x = (A i).adjoint y)
    (htransverse : ∀ j : κ, (B j).adjoint x = (B j).adjoint y) :
    x = y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_iSup_range_sup_eq_top_of_adjoint_eq_zero
    E F A B hcomplete (x - y)
  · intro i
    rw [map_sub, haxis i, sub_self]
  · intro j
    rw [map_sub, htransverse j, sub_self]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
