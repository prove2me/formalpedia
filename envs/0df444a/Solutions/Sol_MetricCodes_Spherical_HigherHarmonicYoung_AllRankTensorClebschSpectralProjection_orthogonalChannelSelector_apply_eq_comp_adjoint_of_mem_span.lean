-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection.orthogonalChannelSelector_apply_eq_comp_adjoint_of_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:46.222992+00:00
-- url     : https://prove2.me/submissions/87426d78-206e-4814-bb45-f460469bc649

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
open MetricCodes.Spherical.HigherHarmonicYoung
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators InnerProductSpace
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankOrthogonalBranchCompleteness
open MetricCodes.Spherical.HigherHarmonicYoung.AllRankCartanCharacteristicInterpolation
namespace MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    {E : ι → Type*}
    [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)]
    [∀ i, FiniteDimensional ℝ (E i)]
    (A : (i : ι) → E i →ₗᵢ[ℝ] V)
    (horth : ∀ i j : ι, i ≠ j →
      ∀ p : E i, ∀ q : E j, ⟪A i p, A j q⟫_ℝ = 0)
    (P : Module.End ℝ V) (selected : ι)
    (hselector : ∀ (j : ι) (p : E j),
      P (A j p) = if selected = j then A j p else 0)
    (x : V)
    (hx : x ∈ (⨆ j : ι, LinearMap.range (A j).toLinearMap)) :
    P x =
      ((A selected).toLinearMap.comp
        (A selected).toLinearMap.adjoint) x := by
  have hadjoint_zero (i j : ι) (hij : i ≠ j) (p : E j) :
      (A i).toLinearMap.adjoint (A j p) = 0 := by
    apply ext_inner_left ℝ
    intro q
    rw [LinearMap.adjoint_inner_right, inner_zero_right]
    exact horth i j hij q p
  have hadjoint_self (i : ι) (p : E i) :
      (A i).toLinearMap.adjoint (A i p) = p :=
    LinearMap.congr_fun (A i).adjoint_comp_self' p
  let Q : Module.End ℝ V :=
    (A selected).toLinearMap.comp (A selected).toLinearMap.adjoint
  have hle : (⨆ j : ι, LinearMap.range (A j).toLinearMap) ≤
      LinearMap.ker (P - Q) := by
    apply iSup_le
    intro j
    rintro _ ⟨p, rfl⟩
    change (P - Q) (A j p) = 0
    simp only [LinearMap.sub_apply, Q, LinearMap.comp_apply]
    rw [hselector j p]
    by_cases h : selected = j
    · subst j
      simp [hadjoint_self]
    · simp [h, hadjoint_zero selected j h p]
  have hzero := hle hx
  change (P - Q) x = 0 at hzero
  exact sub_eq_zero.mp hzero
end MetricCodes.Spherical.HigherHarmonicYoung.AllRankTensorClebschSpectralProjection
