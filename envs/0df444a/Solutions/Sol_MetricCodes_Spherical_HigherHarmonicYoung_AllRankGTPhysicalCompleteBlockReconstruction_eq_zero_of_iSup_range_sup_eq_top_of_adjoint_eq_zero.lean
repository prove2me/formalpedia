-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction.eq_zero_of_iSup_range_sup_eq_top_of_adjoint_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:49.051168+00:00
-- url     : https://prove2.me/submissions/378b2c74-2572-4544-a299-b90ef253f083

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHarmonicYoung_AllRankGTPhysicalCompleteBlockReconstruction_inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero

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
    (y : V)
    (haxis : ∀ i : ι, (A i).adjoint y = 0)
    (htransverse : ∀ j : κ, (B j).adjoint y = 0) :
    y = 0 := by
  apply ext_inner_left ℝ
  intro x
  rw [inner_zero_right]
  have hx : x ∈
      (⨆ i : ι, LinearMap.range (A i)) ⊔
        (⨆ j : κ, LinearMap.range (B j)) := by
    rw [hcomplete]
    trivial
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hx
  rw [inner_add_left,
    inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero E A y haxis u hu,
    inner_eq_zero_of_mem_iSup_range_of_adjoint_eq_zero F B y htransverse v hv,
    add_zero]
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankGTPhysicalCompleteBlockReconstruction
