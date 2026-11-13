-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:35:00.750198+00:00
-- url     : https://prove2.me/submissions/67f494d1-1d11-4e22-ae7c-f24aaee8fb15

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Data.Fintype.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_corrected_cycles
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_uniform_corrected_term_C1
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_global_cubic_remainder_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_independent_circular_realization
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_local_uniform_convexity
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_reference_circular_starting_family

section
-- module Solutions.OAIQ249_SI.Compat
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- d13f23b's `ContinuousLinearMap.IsInvertible.eventually_nhds`: invertible operators form an open set
(SurfaceImmersion primitives, q249). -/
theorem _root_.ContinuousLinearMap.IsInvertible.eventually_nhds {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : E →L[𝕜] F} (hf : f.IsInvertible) : ∀ᶠ g in nhds f, g.IsInvertible := by
  obtain ⟨e, rfl⟩ := hf
  exact Filter.mem_of_superset (ContinuousLinearEquiv.nhds e) (by rintro _ ⟨e', rfl⟩; exact ⟨e', rfl⟩)
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_WeightedBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.WeightedEstimates

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]



lemma WeightedBound.const_smul {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ}
    {m : ℕ} {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (hb : WeightedBound U s m C f) (a : ℝ) :
    WeightedBound U s m (|a| * C) (fun x => a • f x) := by
  intro j hj x hx
  change s ^ j * ‖iteratedFDerivWithin ℝ j (a • f) U x‖ ≤ _
  rw [iteratedFDerivWithin_const_smul_apply
    ((hf.of_le (m := (j : ℕ∞ω)) (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffWithinAt hx)
    hU hx, norm_smul, Real.norm_eq_abs]
  calc
    _ = |a| * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (abs_nonneg _)

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_PositiveBasis
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.RealModes ClosedSurfaceR4.PhaseMean
open Set


lemma basisCoefficient_apply (t u v : ℝ) (H : PhaseMean.Tensor) :
    basisCoefficient t u v H = (H 2 - (u + v) * H 1 + u * v * H 0) / ((t - u) * (t - v)) := by
  simp only [basisCoefficient, smul_apply, add_apply,
    sub_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, div_eq_mul_inv]
  ring



lemma three_slope_decomposition {t₀ t₁ t₂ : ℝ} (h₀₁ : t₀ ≠ t₁)
    (h₀₂ : t₀ ≠ t₂) (h₁₂ : t₁ ≠ t₂) (H : PhaseMean.Tensor) :
    basisCoefficient t₀ t₁ t₂ H • covectorSquare (1, t₀) +
      basisCoefficient t₁ t₀ t₂ H • covectorSquare (1, t₁) +
      basisCoefficient t₂ t₀ t₁ H • covectorSquare (1, t₂) = H := by
  have h10 : t₁ - t₀ ≠ 0 := sub_ne_zero.mpr h₀₁.symm
  have h20 : t₂ - t₀ ≠ 0 := sub_ne_zero.mpr h₀₂.symm
  have h21 : t₂ - t₁ ≠ 0 := sub_ne_zero.mpr h₁₂.symm
  have h01 : t₀ - t₁ ≠ 0 := sub_ne_zero.mpr h₀₁
  have h02 : t₀ - t₂ ≠ 0 := sub_ne_zero.mpr h₀₂
  have h12 : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h₁₂
  ext i
  fin_cases i <;>
    simp [Pi.add_apply, basisCoefficient_apply, covectorSquare] <;>
    field_simp [h10, h20, h21, h01, h02, h12] <;> ring



lemma normalized_numerators_positive {x₀ x₁ x₂ : ℝ}
    (h₀ : x₀ ∈ Ioo (-3 : ℝ) (-2)) (h₁ : x₁ ∈ Ioo (-(1/4) : ℝ) (1/4))
    (h₂ : x₂ ∈ Ioo (2 : ℝ) 3) :
    0 < 1 + x₁*x₂ ∧ 1 + x₀*x₂ < 0 ∧ 0 < 1 + x₀*x₁ := by
  have hx₂ : 0 < x₂ := by linarith [h₂.1]
  have hx₀ : 0 < -x₀ := by linarith [h₀.2]
  have hp₁ := mul_pos (show 0 < x₁ + 1/4 by linarith [h₁.1]) hx₂
  have hp₂ := mul_pos (show 0 < -x₀ - 2 by linarith [h₀.2]) hx₂
  have hp₃ := mul_pos (show 0 < 1/4 - x₁ by linarith [h₁.2]) hx₀
  constructor
  · nlinarith [h₂.2]
  constructor
  · nlinarith [h₂.1]
  · nlinarith [h₀.1]

lemma positive_center_parameters {H : PhaseMean.Tensor} (h₀ : 0 < H 0)
    (hdet : 0 < H 0 * H 2 - (H 1) ^ 2) :
    ∃ β r : ℝ, 0 < r ∧ H 1 = H 0 * β ∧ H 2 = H 0 * (β ^ 2 + r ^ 2) := by
  let β := H 1 / H 0
  let D := H 2 / H 0 - β ^ 2
  have hD : 0 < D := by
    have he : D = (H 0 * H 2 - (H 1) ^ 2) / (H 0) ^ 2 := by
      dsimp [D, β]
      field_simp
    rw [he]
    exact div_pos hdet (sq_pos_of_pos h₀)
  refine ⟨β, Real.sqrt D, Real.sqrt_pos.2 hD, ?_, ?_⟩
  · dsimp [β]
    field_simp
  · rw [Real.sq_sqrt hD.le]
    dsimp [D]
    field_simp
    ring

lemma shifted_numerator (H : PhaseMean.Tensor) {β r : ℝ}
    (h₁ : H 1 = H 0 * β) (h₂ : H 2 = H 0 * (β ^ 2 + r ^ 2)) (u v : ℝ) :
    H 2 - ((β + r*u) + (β + r*v)) * H 1 + (β + r*u)*(β + r*v)*H 0 =
      H 0 * r ^ 2 * (1 + u*v) := by
  rw [h₁, h₂]
  ring

lemma shifted_basis_positive {H : PhaseMean.Tensor} (h₀ : 0 < H 0)
    {β r x₀ x₁ x₂ : ℝ} (hr : 0 < r)
    (h₁ : H 1 = H 0 * β) (h₂ : H 2 = H 0 * (β ^ 2 + r ^ 2))
    (hx₀ : x₀ ∈ Ioo (-3 : ℝ) (-2)) (hx₁ : x₁ ∈ Ioo (-(1/4) : ℝ) (1/4))
    (hx₂ : x₂ ∈ Ioo (2 : ℝ) 3) :
    0 < basisCoefficient (β+r*x₀) (β+r*x₁) (β+r*x₂) H ∧
    0 < basisCoefficient (β+r*x₁) (β+r*x₀) (β+r*x₂) H ∧
    0 < basisCoefficient (β+r*x₂) (β+r*x₀) (β+r*x₁) H := by
  have hnum := normalized_numerators_positive hx₀ hx₁ hx₂
  have h01 : β+r*x₀ < β+r*x₁ := by nlinarith [hx₀.2, hx₁.1]
  have h12 : β+r*x₁ < β+r*x₂ := by nlinarith [hx₁.2, hx₂.1]
  have hp : 0 < H 0 * r ^ 2 := mul_pos h₀ (sq_pos_of_pos hr)
  simp only [basisCoefficient_apply, shifted_numerator H h₁ h₂]
  refine ⟨div_pos (mul_pos hp hnum.1) (mul_pos_of_neg_of_neg (sub_neg.mpr h01)
    (sub_neg.mpr (h01.trans h12))), ?_, ?_⟩
  · exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hp hnum.2.1)
      (mul_neg_of_pos_of_neg (sub_pos.mpr h01) (sub_neg.mpr h12))
  · exact div_pos (mul_pos hp hnum.2.2)
      (mul_pos (sub_pos.mpr (h01.trans h12)) (sub_pos.mpr h12))

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartModel
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinateDomain_open (p : M) : IsOpen (coordinateDomain p) := by
  apply IsOpen.preimage planeCoordinates.symm.continuous
  simpa [extChartAt_target, planeModel] using (chartAt Plane p).open_target

lemma coordinateCenter_mem (p : M) : coordinateCenter p ∈ coordinateDomain p := by
  simp [coordinateCenter, coordinateDomain]

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MetricPullback
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes Set Bundle Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

lemma metricPullback_continuousOn (g : SmoothMetric M) {φ : Base → M} {O : Set Base}
    (hO : IsOpen O) (hφ : ContMDiffOn 𝓘(ℝ, Base) planeModel ∞ φ O) (v w : Base) :
    ContinuousOn (fun x => metricPullback g φ x v w) O := by
  let : RiemannianBundle (fun p : M => TangentSpace planeModel p) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle Plane (fun p : M => TangentSpace planeModel p) :=
    ⟨⟨g.inner,g.contMDiff.continuous,fun _ _ _ => rfl⟩⟩
  have htm := hφ.continuousOn_tangentMapWithin (by simp) hO.uniqueMDiffOn
  have hs (v : Base) : Continuous (fun x : Base =>
      (⟨x,v⟩ : TangentBundle 𝓘(ℝ, Base) Base)) := by
    exact (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, Base)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hv (v : Base) : ContinuousOn (fun x : Base =>
      (⟨φ x,mfderiv 𝓘(ℝ, Base) planeModel φ x v⟩ : TangentBundle planeModel M)) O := by
    have hh := htm.comp (hs v).continuousOn (fun x hx => hx)
    apply hh.congr
    intro x hx
    simp only [Function.comp_apply, tangentMapWithin]
    rw [mfderivWithin_of_mem_nhds (hO.mem_nhds hx)]
  exact (hv v).inner_bundle (hv w)

lemma metricPullback_pos (g : SmoothMetric M) {φ : Base → M} {x : Base}
    (hi : Function.Injective (mfderiv 𝓘(ℝ, Base) planeModel φ x)) {v : Base} (hv : v ≠ 0) :
    0 < metricPullback g φ x v v := by
  apply g.pos
  intro hz
  apply hv
  apply hi
  exact hz.trans (map_zero _).symm

lemma mfderiv_coordinateInverse_center (p : M) :
    mfderiv 𝓘(ℝ, Base) planeModel (coordinateInverse p) (coordinateCenter p) =
      planeCoordinates.symm.toContinuousLinearMap := by
  have hcenter : planeCoordinates.symm (coordinateCenter p) = extChartAt planeModel p p := by
    simp [coordinateCenter]
  have hchart : MDifferentiableAt 𝓘(ℝ, Plane) planeModel
      (extChartAt planeModel p).symm (planeCoordinates.symm (coordinateCenter p)) := by
    rw [hcenter]
    simpa [planeModel, mdifferentiableWithinAt_univ] using
      (contMDiffWithinAt_extChartAt_symm_range_self (I := planeModel)
        (n := (∞ : ℕ∞ω)) p).mdifferentiableWithinAt (by simp)
  rw [coordinateInverse, mfderiv_comp _ hchart
    ((planeCoordinates.symm.contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt]
  rw [hcenter]
  have hid : mfderiv 𝓘(ℝ, Plane) planeModel (extChartAt planeModel p).symm
      (extChartAt planeModel p p) = ContinuousLinearMap.id ℝ Plane := by
    simpa [planeModel] using! mfderivWithin_range_extChartAt_symm (I := planeModel) (x := p)
  rw [hid]
  ext v
  change mfderiv 𝓘(ℝ, Base) 𝓘(ℝ, Plane) planeCoordinates.symm (coordinateCenter p) v =
    planeCoordinates.symm v
  rw [mfderiv_eq_fderiv, planeCoordinates.symm.fderiv]
  rfl

lemma coordinateMetric_continuousAt_center (g : SmoothMetric M) (p : M) :
    ContinuousAt (coordinateMetric g p) (coordinateCenter p) := by
  apply continuousAt_pi.mpr
  intro i
  exact (metricPullback_continuousOn g (coordinateDomain_open p)
    (coordinateInverse_smoothOn p) _ _).continuousAt
      ((coordinateDomain_open p).mem_nhds (coordinateCenter_mem p))

lemma coordinateMetric_evaluate (g : SmoothMetric M) (p : M) (x v w : Base) :
    PhaseMean.evaluate (coordinateMetric g p x) v w =
      metricPullback g (coordinateInverse p) x v w := by
  let D : Base →L[ℝ] TangentSpace planeModel (coordinateInverse p x) :=
    mfderiv 𝓘(ℝ, Base) planeModel (coordinateInverse p) x
  change PhaseMean.evaluate (fun i => g.inner (coordinateInverse p x)
      (D (PhaseMean.firstDirection i)) (D (PhaseMean.secondDirection i))) v w =
    g.inner (coordinateInverse p x) (D v) (D w)
  have he (v : Base) : v = v.1 • dx + v.2 • dy := by
    ext <;> simp [dx,dy]
  conv_rhs => rw [he v, he w]
  simp only [PhaseMean.evaluate,
    PhaseMean.firstDirection, PhaseMean.secondDirection, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead, Function.comp_apply,
    map_add, map_smul, add_apply,
    smul_apply, smul_eq_mul]
  rw [g.symm _
    (D dy) (D dx)]
  dsimp
  ring

lemma tensor_positive_iff (H : PhaseMean.Tensor) :
    (∀ v : Base, v ≠ 0 → 0 < PhaseMean.evaluate H v v) ↔
      0 < H 0 ∧ 0 < H 0 * H 2 - (H 1)^2 := by
  constructor
  · intro h
    have h₀ : 0 < H 0 := by
      simpa [PhaseMean.evaluate] using h (1, 0) (by simp)
    have hv : (-H 1, H 0) ≠ (0 : Base) := by
      intro he
      have he' := congrArg Prod.snd he
      exact h₀.ne' he'
    have hh := h (-H 1, H 0) hv
    have he : PhaseMean.evaluate H (-H 1, H 0) (-H 1, H 0) = H 0 * (H 0 * H 2 - (H 1)^2) := by
      simp only [PhaseMean.evaluate]
      ring
    rw [he] at hh
    exact ⟨h₀, (mul_pos_iff_of_pos_left h₀).mp hh⟩
  · rintro ⟨h₀, hd⟩ v hv
    have he : H 0 * PhaseMean.evaluate H v v =
        (H 0 * v.1 + H 1 * v.2)^2 + (H 0 * H 2 - (H 1)^2) * v.2^2 := by
      simp only [PhaseMean.evaluate]
      ring
    apply (mul_pos_iff_of_pos_left h₀).mp
    rw [he]
    by_cases hv₂ : v.2 = 0
    · have hv₁ : v.1 ≠ 0 := by
        intro hz
        apply hv
        exact Prod.ext hz hv₂
      simp only [hv₂, mul_zero, add_zero, zero_pow (by decide : 2 ≠ 0)]
      exact sq_pos_of_ne_zero (mul_ne_zero h₀.ne' hv₁)
    · exact add_pos_of_nonneg_of_pos (sq_nonneg _)
        (mul_pos hd (sq_pos_of_ne_zero hv₂))


lemma coordinateMetric_positive_center (g : SmoothMetric M) (p : M) :
    0 < coordinateMetric g p (coordinateCenter p) 0 ∧
    0 < coordinateMetric g p (coordinateCenter p) 0 *
      coordinateMetric g p (coordinateCenter p) 2 -
      (coordinateMetric g p (coordinateCenter p) 1)^2 := by
  apply (tensor_positive_iff _).mp
  intro v hv
  rw [coordinateMetric_evaluate]
  apply metricPullback_pos g _ hv
  rw [mfderiv_coordinateInverse_center]
  exact planeCoordinates.symm.injective

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SquarePartition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  {ι : Type*} [Fintype ι]




theorem exists_smooth_square_partition (U : ι → Set M) (hU : ∀ i, IsOpen (U i))
    (hcover : (Set.univ : Set M) ⊆ ⋃ i, U i) :
    ∃ ψ : ι → M → ℝ,
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  classical
  obtain ⟨ρ,hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E) isClosed_univ U hU hcover
  let σ : M → ℝ := fun p => ∑ i, (ρ i p)^2
  have hsum (p : M) : ∑ i, ρ i p = 1 := by
    simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one (mem_univ p)
  have hσ (p : M) : 0 < σ p := by
    have hnon : 0 ≤ σ p := Finset.sum_nonneg (fun i _ => sq_nonneg (ρ i p))
    by_contra hn
    have hz : σ p = 0 := le_antisymm (not_lt.mp hn) hnon
    have hi : ∀ i, ρ i p = 0 := by
      intro i
      have hs := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j (_ : j ∈ Finset.univ) => sq_nonneg (ρ j p))).mp hz i (Finset.mem_univ i)
      exact sq_eq_zero_iff.mp hs
    have hf := hsum p
    simp only [hi, Finset.sum_const_zero] at hf
    norm_num at hf
  have hsmoothσ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ σ := by
    exact contMDiff_finsetSum (fun i _ => (ρ i).contMDiff.pow 2)
  have hsmoothsqrt : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun p => Real.sqrt (σ p)) := by
    intro p
    exact (Real.contDiffAt_sqrt (hσ p).ne').contMDiffAt.comp p (hsmoothσ p)
  let ψ : ι → M → ℝ := fun i p => ρ i p / Real.sqrt (σ p)
  have hψsupp (i : ι) : tsupport (ψ i) ⊆ tsupport (ρ i) := by
    apply closure_mono
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    exact fun hn => hp (by simp [ψ, hn])
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).contMDiff.div₀ hsmoothsqrt (fun p => (Real.sqrt_pos.mpr (hσ p)).ne')
  · intro i
    exact (hψsupp i).trans (hρ i)
  · intro i
    exact (isClosed_tsupport (ψ i)).isCompact
  · intro i p
    exact div_nonneg (ρ.nonneg i p) (Real.sqrt_nonneg _)
  · intro p
    calc
      ∑ i, (ψ i p)^2 = (∑ i, (ρ i p)^2) / (Real.sqrt (σ p))^2 := by
        simp only [ψ, div_pow, Finset.sum_div]
      _ = σ p / σ p := by rw [Real.sq_sqrt (hσ p).le]
      _ = 1 := div_self (hσ p).ne'

end ClosedSurfaceR4.PhaseGeometry

namespace ClosedSurfaceR4.PhaseGeometry
open Set Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]



theorem exists_finite_smooth_square_partition (U : M → Set M)
    (hU : ∀ p, IsOpen (U p)) (hp : ∀ p, p ∈ U p) :
    ∃ (t : Finset M) (ψ : t → M → ℝ),
      (∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (ψ i)) ∧
      (∀ i, tsupport (ψ i) ⊆ U i) ∧
      (∀ i, HasCompactSupport (ψ i)) ∧
      (∀ i p, 0 ≤ ψ i p) ∧ (∀ p, ∑ i, (ψ i p)^2 = 1) := by
  classical
  have hc : (univ : Set M) ⊆ ⋃ p, U p := fun p _ => mem_iUnion.mpr ⟨p, hp p⟩
  obtain ⟨t,ht⟩ := isCompact_univ.elim_finite_subcover U hU hc
  have hct : (univ : Set M) ⊆ ⋃ i : t, U i := by
    intro p _
    obtain ⟨i,hi,hpi⟩ := mem_iUnion₂.mp (ht (mem_univ p))
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hpi⟩
  obtain ⟨ψ,hψ⟩ := exists_smooth_square_partition (E := E) (fun i : t => U i)
    (fun i => hU i) hct
  exact ⟨t,ψ,hψ⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ChartTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma coordinateChart_apply (p q : M) : coordinateChart p q = chartCoordinates p q := rfl

variable [IsManifold planeModel ∞ M]

lemma coordinateChart_smoothOn (p : M) :
    ContMDiffOn planeModel 𝓘(ℝ,SmallModes.Base) ∞ (coordinateChart p) (coordinateChart p).source := by
  rw [coordinateChart_source]
  exact planeCoordinates.contDiff.contMDiff.comp_contMDiffOn contMDiffOn_chart

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_AtlasPhases
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Filter
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]


lemma phaseLinear_apply (ξ x : SmallModes.Base) : phaseLinear ξ x = ξ.1*x.1+ξ.2*x.2 := rfl

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_Main
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4
open SmallModes RealModes PhaseGeometry Set Bundle Manifold Filter


variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]



theorem IsSmoothIsometricImmersion.mfderiv_injective {g : SmoothMetric M}
    {F : M → Space} (h : IsSmoothIsometricImmersion M g F) (p : M) :
    Function.Injective (mfderiv planeModel spaceModel F p) := by
  intro v w hvw
  apply sub_eq_zero.mp
  by_contra hne
  have hv : mfderiv planeModel spaceModel F p (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hinner := h.2 p (v - w) (v - w)
  rw [hv, inner_zero_left] at hinner
  exact (ne_of_gt (g.pos p (v - w) hne)) hinner.symm



theorem PhaseGeometry.positive_tensor_has_basis {H : PhaseMean.Tensor}
    (h₀ : 0 < H 0) (hdet : 0 < H 0 * H 2 - (H 1)^2) :
    ∃ P : PhaseBasis, ∀ j, 0 < P.Q j H := by
  obtain ⟨β,r,hr,h₁,h₂⟩ := positive_center_parameters h₀ hdet
  let t₀ := β + r * (-(5/2) : ℝ)
  let t₁ := β + r * (0 : ℝ)
  let t₂ := β + r * (5/2 : ℝ)
  have h01 : t₀ < t₁ := by dsimp [t₀,t₁] <;> linarith
  have h12 : t₁ < t₂ := by dsimp [t₁,t₂] <;> linarith
  have hp := shifted_basis_positive h₀ hr h₁ h₂
    (show (-(5/2) : ℝ) ∈ Ioo (-3 : ℝ) (-2) by norm_num)
    (show (0 : ℝ) ∈ Ioo (-(1/4) : ℝ) (1/4) by norm_num)
    (show (5/2 : ℝ) ∈ Ioo (2 : ℝ) 3 by norm_num)
  let ξ : Fin 3 → Base := ![(1,t₀),(1,t₁),(1,t₂)]
  let Q : Fin 3 → PhaseMean.Tensor →L[ℝ] ℝ :=
    ![basisCoefficient t₀ t₁ t₂, basisCoefficient t₁ t₀ t₂, basisCoefficient t₂ t₀ t₁]
  have hd : ∀ A, ∑ j, Q j A • covectorSquare (ξ j) = A := by
    intro A
    simpa only [Fin.sum_univ_three,ξ,Q,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
      Fin.succ_zero_eq_one] using
      three_slope_decomposition h01.ne (h01.trans h12).ne h12.ne A
  have hn : ∀ j, ξ j ≠ 0 := by
    intro j
    fin_cases j <;> simp [ξ]
  refine ⟨⟨ξ,Q,hd,hn⟩,?_⟩
  intro j
  fin_cases j
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2



end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldFreeIncrement
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Local free oscillations as maps on the surface

The finite-mode construction takes place in coordinates. These lemmas
extend its supported output by zero on the surface, preserving smoothness
and support. This is the first globalization step for the small increments.
-/

noncomputable section

namespace ClosedSurfaceR4

open Set Manifold
open scoped ContDiff Topology
open SmallModes RealModes RootMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

/-- Extension by zero across a closed support lying inside the smooth chart. -/
theorem contMDiff_indicator_of_support {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {O S : Set M} {Z : M → V}
    (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    (hZ : ContMDiffOn planeModel 𝓘(ℝ, V) ∞ Z O)
    (hz : ∀ x ∈ O, x ∉ S → Z x = 0) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (O.indicator Z) ∧
      tsupport (O.indicator Z) ⊆ S := by
  classical
  have hs : tsupport (O.indicator Z) ⊆ S := by
    apply closure_minimal _ hS
    intro x hx
    by_contra hxS
    by_cases hxO : x ∈ O
    · exact hx (by rw [indicator_of_mem hxO, hz x hxO hxS])
    · exact hx (indicator_of_notMem hxO Z)
  refine ⟨contMDiff_of_tsupport (fun x hx => ?_), hs⟩
  have hxO : x ∈ O := hSO (hs hx)
  apply ((hZ x hxO).contMDiffAt (hO.mem_nhds hxO)).congr_of_eventuallyEq
  filter_upwards [hO.mem_nhds hxO] with y hy
  exact indicator_of_mem hy Z

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite chart data with inner and outer cutoffs for smoothing on a closed
surface. All chart and cutoff data are chosen independently of the input. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

variable [IsManifold planeModel ∞ M]

variable [T2Space M] [CompactSpace M]

/-- A compact smooth surface admits fixed finite smoothing chart data. -/
theorem exists_smoothingAtlas : Nonempty (SmoothingAtlas M) := by
  classical
  obtain ⟨t, ψ, hψ, hsupp, _, _, hsum⟩ :=
    PhaseGeometry.exists_finite_smooth_square_partition (E := Plane)
      (fun p : M => (chart p).source) (fun p => (chart p).open_source)
      (fun p => by rw [chart_source]; exact mem_chart_source Plane p)
  have hout : ∀ i : t, ∃ χ : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ χ ∧
      tsupport χ ⊆ (chart (i : M)).source ∧
      ∀ x ∈ tsupport (ψ i), χ x = 1 := by
    intro i
    have hc : IsCompact (tsupport (ψ i)) := (isClosed_tsupport _).isCompact
    obtain ⟨O, hO, hKO, hOc⟩ := hc.exists_isOpen_closure_subset
      ((chart (i : M)).open_source.mem_nhdsSet.mpr (hsupp i))
    obtain ⟨χ, hχ, _, hχs, hχone⟩ :=
      exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
        hO (isClosed_tsupport (ψ i)) hKO
    refine ⟨χ, hχ, ?_, fun x hx => (hχone x).mp hx⟩
    change closure (Function.support χ) ⊆ _
    rw [hχs]
    exact hOc
  choose χ hχ hχs hχone using hout
  exact ⟨⟨t, ψ, χ, hψ, hsupp, hχ, hχs, hχone, hsum⟩⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothingLinearity
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global smoothing construction is linear on smooth maps. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma localize_smul (p : M) (ψ : M → ℝ) (a : ℝ) (f : M → V) :
    localize p ψ (a • f) = a • localize p ψ f := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_smul, mul_comm]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness and elementary norm operations for actual global metric tensors. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundDualSmul
variable (A : SmoothingAtlas M)
include A

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricBoundFiberSpace
local instance metricBoundSectionNormed_r47b1a3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_r47b1a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_add {T S : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p)))
    (hS : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (S p)))
    {s C D : ℝ} {m : ℕ} (hs : 0 ≤ s)
    (hbT : A.TensorWeightedBound s m C T) (hbS : A.TensorWeightedBound s m D S) :
    A.TensorWeightedBound s m (C+D) (T+S) := by
  intro i
  change WeightedEstimates.WeightedBound univ s m (C+D) (A.bundleLocalize A.tensorTriv i (T+S))
  rw [A.bundleLocalize_add]
  exact (hbT i).add uniqueDiffOn_univ hs
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT).contDiffOn
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hS).contDiffOn (hbS i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ConvexQuadraticPhase
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual convex phases used in finite primitive preparation. Their
coordinate covariant Hessians are uniformly positive on a sufficiently
small disk when the metric connection has a fixed bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma convexQuadraticPhase_hasFDerivAt (ell : Base) (L : ℝ) (p : Base) :
    HasFDerivAt (convexQuadraticPhase ell L) (phaseLinear (ell + L • p)) p := by
  have h1 := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := p)
  have h2 := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := p)
  have hh := (phaseLinear ell).hasFDerivAt (x := p) |>.add
    (((h1.pow 2).add (h2.pow 2)).const_mul (L / 2))
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [add_apply, smul_apply, phaseLinear_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    two_smul, smul_eq_mul]
  ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseBasisPerturbation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coefficient forms for nearby phase covectors. The inverse
operator constructs the new decomposition and preserves compact positive
cone margins. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma perturbedPhaseOperator_self (P : PhaseBasis) :
    perturbedPhaseOperator P P.ξ = ContinuousLinearMap.id ℝ PhaseMean.Tensor := by
  apply ContinuousLinearMap.ext
  intro H
  exact (perturbedPhaseOperator_apply P P.ξ H).trans (P.decomposition H)

lemma perturbedPhaseOperator_smooth (P : PhaseBasis) :
    ContDiff ℝ ∞ (perturbedPhaseOperator P) := by
  apply ContDiff.sum
  intro i _
  apply contDiff_const.smulRight
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> simp only [covectorSquare, Matrix.cons_val_zero',
    Matrix.cons_val_succ'] <;> fun_prop

lemma perturbedPhaseCoefficient_self (P : PhaseBasis) (i : Fin 3) :
    perturbedPhaseCoefficient P P.ξ i = P.Q i := by
  simp only [perturbedPhaseCoefficient, perturbedPhaseOperator_self,
    ContinuousLinearMap.inverse_id, ContinuousLinearMap.comp_id]

lemma perturbedPhaseCoefficient_smoothAt (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : (perturbedPhaseOperator P xi).IsInvertible) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z => perturbedPhaseCoefficient P z i) xi :=
  contDiffAt_const.clm_comp
    (hxi.contDiffAt_map_inverse.comp xi (perturbedPhaseOperator_smooth P).contDiffAt)

lemma positivePhaseParameters_open (P : PhaseBasis) : IsOpen (positivePhaseParameters P) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hA : ∀ᶠ w in 𝓝 z, (perturbedPhaseOperator P w.1).IsInvertible :=
    ((perturbedPhaseOperator_smooth P).continuous.comp continuous_fst).continuousAt.eventually
      hz.1.eventually_nhds
  have hxi : ∀ᶠ w in 𝓝 z, ∀ i, w.1 i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact ((continuous_apply i).comp continuous_fst).continuousAt.eventually_ne (hz.2.1 i)
  have hQ : ∀ᶠ w in 𝓝 z, ∀ i, 0 < perturbedPhaseCoefficient P w.1 i w.2 := by
    rw [Filter.eventually_all]
    intro i
    have hc : ContinuousAt (fun w : (Fin 3 → Base) × PhaseMean.Tensor =>
        perturbedPhaseCoefficient P w.1 i w.2) z :=
      (((perturbedPhaseCoefficient_smoothAt P hz.1 i).comp z contDiffAt_fst).clm_apply
        contDiffAt_snd).continuousAt
    exact hc.eventually (lt_mem_nhds (hz.2.2 i))
  exact hA.and (hxi.and hQ)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SpatialPhaseBasis
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual point-dependent phase bases. Outside the region of invertible
phase triples a fixed basis supplies harmless global values. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma resolvedPhaseBasis_coefficients (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : admissiblePhaseCovectors P xi) (i : Fin 3) :
    (resolvedPhaseBasis P xi).Q i = perturbedPhaseCoefficient P xi i := by
  simp only [resolvedPhaseBasis,dite_eq_left hxi]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredConvexPhase
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convex phases centered at the actual coordinate center of a circular
patch. The connection is evaluated at the original point, so translation
of the phase does not silently translate the metric. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma centeredConvexPhase_hasFDerivAt (ell : Base) (L : ℝ) (c p : Base) :
    HasFDerivAt (centeredConvexPhase ell L c) (phaseLinear (ell+L • (p-c))) p := by
  have ht : HasFDerivAt (fun x : Base => x-c) (ContinuousLinearMap.id ℝ Base) p :=
    (hasFDerivAt_id p).sub_const c
  simpa only [centeredConvexPhase,Function.comp_def,ContinuousLinearMap.comp_id] using!
    (convexQuadraticPhase_hasFDerivAt ell L (p-c)).comp p ht

lemma centeredConvexPhase_phaseDerivative (ell : Base) (L : ℝ) (c p : Base) :
    phaseDerivative (centeredConvexPhase ell L c) p = ell+L • (p-c) := by
  unfold phaseDerivative
  rw [(centeredConvexPhase_hasFDerivAt ell L c p).fderiv]
  ext <;> simp [phaseLinear_apply,dx,dy]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactPhaseChart
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A single smooth inverse representative on a neighborhood of a compact
phase-chart region, without changing its forward coordinate map. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

theorem extend_compact_chart_inverse (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set Base} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ d : OpenPartialHomeomorph Base Base, K ⊆ d.source ∧
      (d : Base → Base) = e ∧ d.source ⊆ e.source ∧ d.target ⊆ e.target ∧
      ContDiff ℝ ∞ d ∧ ContDiff ℝ ∞ d.symm := by
  obtain ⟨W,hW,hKW,hWe,B,hB,hBE⟩ := CollarVelocity.compact_smooth_extension
    (hK.image he.continuous) e.open_target (image_subset_iff.mpr (fun x hx => e.map_source (hKe hx))) hi
  let d : OpenPartialHomeomorph Base Base := {
    toFun := e
    invFun := B
    source := e.source ∩ e ⁻¹' W
    target := e.target ∩ W
    map_source' := fun x hx => ⟨e.map_source hx.1,hx.2⟩
    map_target' := by
      intro y hy
      rw [hBE hy.2]
      refine ⟨e.map_target hy.1,?_⟩
      change e (e.symm y) ∈ W
      simpa only [e.right_inv hy.1] using hy.2
    left_inv' := by
      intro x hx
      rw [hBE hx.2]
      exact e.left_inv hx.1
    right_inv' := by
      intro y hy
      rw [hBE hy.2]
      exact e.right_inv hy.1
    open_source := e.open_source.inter (hW.preimage he.continuous)
    open_target := e.open_target.inter hW
    continuousOn_toFun := he.continuous.continuousOn
    continuousOn_invFun := hB.continuous.continuousOn
  }
  exact ⟨d,fun x hx => ⟨hKe hx,hKW (mem_image_of_mem e hx)⟩,
    rfl,fun _ hx => hx.1,fun _ hx => hx.1,he,hB⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CenteredParabolicChart
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One explicit nonlinear phase chart on a whole centered neighborhood. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma centeredPhaseCoordinates_apply (ell : Base) (hell : ell ≠ 0) (c x : Base) :
    centeredPhaseCoordinates ell hell c x = phaseEquiv ell hell (x-c) := by
  rfl

lemma centeredPhaseCoordinates_smooth (ell : Base) (hell : ell ≠ 0) (c : Base) :
    ContDiff ℝ ∞ (centeredPhaseCoordinates ell hell c) :=
  (phaseEquiv ell hell).contDiff.comp (contDiff_id.sub contDiff_const)

lemma centeredPhaseCoordinates_inverse_smooth (ell : Base) (hell : ell ≠ 0) (c : Base) :
    ContDiff ℝ ∞ (centeredPhaseCoordinates ell hell c).symm := by
  change ContDiff ℝ ∞ (fun x => (phaseEquiv ell hell).symm x - -c)
  exact (phaseEquiv ell hell).symm.contDiff.sub contDiff_const

lemma centeredParabolicChart_phase (ell : Base) (hell : ell ≠ 0) (L : ℝ) (hL : L ≠ 0)
    (c x : Base) :
    (centeredParabolicChart ell hell L hL c x).1 = centeredConvexPhase ell L c x := by
  change (parabolicPhaseMap (L/phaseCovectorSquare ell) (centeredPhaseCoordinates ell hell c x)).1 = _
  rw [centeredPhaseCoordinates_apply]
  simp only [parabolicPhaseMap,phaseEquiv_apply,Prod.fst_sub,Prod.snd_sub,
    centeredConvexPhase,convexQuadraticPhase,phaseLinear_apply,phaseCovectorSquare]
  have hA : ell.1^2+ell.2^2 ≠ 0 := (phaseCovectorSquare_pos hell).ne'
  field_simp [hA]
  ring

lemma centeredParabolicChart_smooth (ell : Base) (hell : ell ≠ 0) (L : ℝ) (hL : L ≠ 0)
    (c : Base) : ContDiff ℝ ∞ (centeredParabolicChart ell hell L hL c) :=
  (parabolicPhaseMap_smooth _).comp (centeredPhaseCoordinates_smooth ell hell c)

lemma centeredParabolicChart_inverse_smooth (ell : Base) (hell : ell ≠ 0)
    (L : ℝ) (hL : L ≠ 0) (c : Base) :
    ContDiffOn ℝ ∞ (centeredParabolicChart ell hell L hL c).symm
      (centeredParabolicChart ell hell L hL c).target := by
  exact (centeredPhaseCoordinates_inverse_smooth ell hell c).comp_contDiffOn
    (parabolicPhaseInverse_smooth _)

lemma centeredParabolicChart_source (ell : Base) (hell : ell ≠ 0) (L : ℝ) (hL : L ≠ 0)
    (c x : Base) :
    x ∈ (centeredParabolicChart ell hell L hL c).source ↔
      0 < phaseCovectorSquare ell+L*phaseLinear ell (x-c) := by
  change 0 < 1+(L/phaseCovectorSquare ell)*(phaseEquiv ell hell (x-c)).1 ↔ _
  rw [← mul_pos_iff_of_pos_left (phaseCovectorSquare_pos hell)]
  have hh : phaseCovectorSquare ell*(1+(L/phaseCovectorSquare ell)*(phaseEquiv ell hell (x-c)).1) =
      phaseCovectorSquare ell+L*phaseLinear ell (x-c) := by
    change phaseCovectorSquare ell*(1+(L/phaseCovectorSquare ell)*phaseLinear ell (x-c)) = _
    field_simp [(phaseCovectorSquare_pos hell).ne']
  rw [hh]

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_UniformCenteredCharts
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The phase-chart radius is fixed before choosing the independent phase
parameters and the centers. This resolves that order in finite preparation. -/
noncomputable section
open Set Metric
open scoped ContDiff Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma abs_phaseLinear_le (ell v : Base) : |phaseLinear ell v| ≤ 2*‖ell‖*‖v‖ := by
  calc
    _ ≤ |ell.1*v.1|+|ell.2*v.2| := abs_add_le _ _
    _ = |ell.1| * |v.1| + |ell.2| * |v.2| := by rw [abs_mul,abs_mul]
    _ ≤ ‖ell‖*‖v‖+‖ell‖*‖v‖ := by
      gcongr
      · exact norm_fst_le ell
      · exact norm_fst_le v
      · exact norm_snd_le ell
      · exact norm_snd_le v
    _ = _ := by ring

theorem compact_uniform_centered_charts {P : Set Base} (hP : IsCompact P)
    (hP0 : ∀ ell ∈ P, ell ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∃ r : ℝ, 0 < r ∧ ∀ ell ∈ P, ∀ c : Base,
      ∃ e : OpenPartialHomeomorph Base Base,
        (∀ x, (e x).1 = centeredConvexPhase ell L c x) ∧
        ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
        closedBall c r ⊆ e.source := by
  have hA : Continuous (phaseCovectorSquare : Base → ℝ) := by
    unfold phaseCovectorSquare
    fun_prop
  obtain ⟨d,hd,hbound⟩ := hP.exists_forall_le' hA.continuousOn
    (fun ell hell => phaseCovectorSquare_pos (hP0 ell hell))
  obtain ⟨R₀,hR₀⟩ := hP.isBounded.subset_ball (0 : Base)
  let R := |R₀|+1
  have hR : 0 < R := by dsimp [R] <;> positivity
  have hnorm : ∀ ell ∈ P, ‖ell‖ ≤ R := by
    intro ell hell
    have hh := hR₀ hell
    rw [mem_ball,dist_zero_right] at hh
    exact hh.le.trans (by dsimp [R] <;> linarith [le_abs_self R₀])
  let r := d/(1+2*L*R)
  have hden : 0 < 1+2*L*R := by positivity
  have hr : 0 < r := div_pos hd hden
  have heq : (1+2*L*R)*r = d := by
    dsimp [r]
    field_simp
  have hsmall : L*(2*R*r) < d := by nlinarith
  refine ⟨r,hr,?_⟩
  intro ell hell c
  let e := centeredParabolicChart ell (hP0 ell hell) L hL.ne' c
  have hcover : closedBall c r ⊆ e.source := by
    intro x hx
    rw [mem_closedBall,dist_eq_norm] at hx
    apply (centeredParabolicChart_source ell (hP0 ell hell) L hL.ne' c x).mpr
    have hu : |phaseLinear ell (x-c)| ≤ 2*R*r :=
      (abs_phaseLinear_le ell (x-c)).trans (by gcongr; exact hnorm ell hell)
    have hlower := neg_le_of_abs_le hu
    have hb := hbound ell hell
    nlinarith
  obtain ⟨f,hfcover,hfe,_,_,hf,hfi⟩ := extend_compact_chart_inverse e
    (centeredParabolicChart_smooth ell (hP0 ell hell) L hL.ne' c)
    (centeredParabolicChart_inverse_smooth ell (hP0 ell hell) L hL.ne' c)
    (isCompact_closedBall c r) hcover
  exact ⟨f,fun x => by rw [hfe]; exact centeredParabolicChart_phase ell (hP0 ell hell) L hL.ne' c x,
    hf,hfi,hfcover⟩

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_JetPhaseChartFromReal
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The whole-disk real phase charts in the coordinate representation used
by the nonlinear primitive construction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates SmallModes

lemma jetPhaseChart_apply (e : OpenPartialHomeomorph Base Base) (x : JetPolynomial.Base) :
    jetPhaseChart e x = baseEquiv.symm (e (baseEquiv x)) := rfl

lemma jetPhaseChart_source (e : OpenPartialHomeomorph Base Base) :
    (jetPhaseChart e).source = baseEquiv ⁻¹' e.source := rfl

lemma jetPhaseChart_smooth {e : OpenPartialHomeomorph Base Base} (he : ContDiff ℝ ∞ e) :
    ContDiff ℝ ∞ (jetPhaseChart e) :=
  baseEquiv.symm.contDiff.comp (he.comp baseEquiv.contDiff)

lemma jetPhaseChart_symm_smooth {e : OpenPartialHomeomorph Base Base}
    (hi : ContDiff ℝ ∞ e.symm) : ContDiff ℝ ∞ (jetPhaseChart e).symm :=
  baseEquiv.symm.contDiff.comp (hi.comp baseEquiv.contDiff)

end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LocalReferencePhaseBasis
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A positive reference phase basis on a neighborhood of each center,
with its quadratic part fixed by the metric convexity estimate. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

theorem local_reference_phase_basis (g : SmoothMetric M) (p : M)
    (P : PhaseBasis) (hP : ∀ j, 0 < P.Q j (coordinateMetric g p (coordinateCenter p))) (L : ℝ) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ U ⊆ (coordinateChart p).source ∧
      ∀ q ∈ U,
        admissiblePhaseCovectors P (fun j => phaseDerivative
          (centeredConvexPhase (P.ξ j) L (coordinateChart p p)) (coordinateChart p q)) ∧
        ∀ j, 0 < (centeredSpatialBasis P P.ξ L (coordinateChart p p)
          (coordinateChart p q)).Q j (coordinateMetric g p (coordinateChart p q)) := by
  let xi : Base → Fin 3 → Base := fun x j =>
    phaseDerivative (centeredConvexPhase (P.ξ j) L (coordinateCenter p)) x
  have hxi : Continuous xi := by
    apply continuous_pi
    intro j
    simp only [xi,centeredConvexPhase_phaseDerivative]
    fun_prop
  have hself : xi (coordinateCenter p) = P.ξ := by
    funext j
    simp only [xi,centeredConvexPhase_phaseDerivative,sub_self,smul_zero,add_zero]
  have hbase : (xi (coordinateCenter p),coordinateMetric g p (coordinateCenter p)) ∈
      positivePhaseParameters P := by
    rw [hself]
    refine ⟨?_,P.nonzero,?_⟩
    · rw [perturbedPhaseOperator_self]
      exact ⟨ContinuousLinearEquiv.refl ℝ PhaseMean.Tensor,rfl⟩
    · intro j
      simpa only [perturbedPhaseCoefficient_self] using hP j
  have hn := (hxi.continuousAt.prodMk (coordinateMetric_continuousAt_center g p)).eventually
    ((positivePhaseParameters_open P).mem_nhds hbase)
  obtain ⟨W,hWsub,hW,hcW⟩ := mem_nhds_iff.mp hn
  let U : Set M := (coordinateChart p).source ∩ (coordinateChart p) ⁻¹' W
  have hc : coordinateChart p p = coordinateCenter p := by
    simp [coordinateChart_apply,chartCoordinates,coordinateCenter,planeModel]
  refine ⟨U,(coordinateChart p).isOpen_inter_preimage hW,⟨?_,?_⟩,fun q hq => hq.1,?_⟩
  · rw [coordinateChart_source]; exact mem_chart_source Plane p
  · change coordinateChart p p ∈ W
    rwa [hc]
  · intro q hq
    have hm := hWsub hq.2
    change (xi (coordinateChart p q),coordinateMetric g p (coordinateChart p q)) ∈
      positivePhaseParameters P at hm
    have ha : admissiblePhaseCovectors P (xi (coordinateChart p q)) := ⟨hm.1,hm.2.1⟩
    rw [hc]
    refine ⟨ha,?_⟩
    intro j
    change 0 < (resolvedPhaseBasis P (xi (coordinateChart p q))).Q j _
    rw [resolvedPhaseBasis_coefficients P ha]
    exact hm.2.2 j

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ChartedAtlasQuadraticResidual
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact zero-phase residual of the actual charted free family. -/
noncomputable section
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold Bundle PhaseMean PhaseGeometry WeightedEstimates FiniteMean
open JetPolynomial (Base)
open JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.quadraticAtlasSectionNormed
local instance quadraticAtlasSectionSpace_r47b1a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma tensorWeightedBound_const_smul
    {u : ∀ x : M, CovariantTwoTensor x}
    (hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun x => TotalSpace.mk' TensorFiber x (u x)))
    {s C : ℝ} {m : ℕ}
    (hb : A.TensorWeightedBound s m C u) (a : ℝ) :
    A.TensorWeightedBound s m (|a| * C) (a • u) := by
  intro i
  have hb' := (hb i).const_smul uniqueDiffOn_univ
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hu).contDiffOn a
  change _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound univ s m (|a| * C) (A.bundleLocalize A.tensorTriv i (a • u))
  rw [A.bundleLocalize_smul]
  exact hb'

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InitialInputBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite initial input estimates for the scalar-contracted map. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance initialBoundFiberNormed_r47b1a3_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_r47b1a3_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd_r47b1a3_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_r47b1a3_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialBoundSectionNormed_r47b1a3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_r47b1a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma space_smul_contMDiff {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    ContMDiff planeModel spaceModel ∞ (a • F) :=
  (a • ContinuousLinearMap.id ℝ Space).contDiff.contMDiff.comp hF

namespace SmoothingAtlas
local instance initialBoundFiberNormed_r47b1a3_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_r47b1a3_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd_r47b1a3_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_r47b1a3_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance initialBoundSectionNormed_r47b1a3_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_r47b1a3_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma weightedBound_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C : ℝ} {m : ℕ}
    (hb : A.WeightedBound s m C F) (a : ℝ) :
    A.WeightedBound s m (|a| * C) (a • F) := by
  intro i
  rw [localize_smul]
  exact (hb i).const_smul uniqueDiffOn_univ
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn a

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularFlatBump
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flat cutoffs for the actual circular disks in primitive preparation.
Their centers and radii are smooth parameters. -/
noncomputable section
open Set Function Filter
open scoped Topology
open scoped ContDiff

namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

lemma circularRadiusSquared_smooth (c : Base) :
    ContDiff ℝ ∞ (circularRadiusSquared c) := by
  unfold circularRadiusSquared
  fun_prop

lemma circularFlatBump_smooth (c : Base) (r : ℝ) :
    ContDiff ℝ ∞ (circularFlatBump c r) := by
  exact expNegInvGlue.contDiff.comp (contDiff_const.sub (circularRadiusSquared_smooth c))

lemma circularFlatBump_nonneg (c : Base) (r : ℝ) (p : Base) :
    0 ≤ circularFlatBump c r p := expNegInvGlue.nonneg _

lemma circularFlatBump_zero_iff (c : Base) (r : ℝ) (p : Base) :
    circularFlatBump c r p = 0 ↔ r^2 ≤ circularRadiusSquared c p := by
  simp only [circularFlatBump, expNegInvGlue.zero_iff_nonpos, sub_nonpos]

lemma circularFlatBump_pos_iff (c : Base) (r : ℝ) (p : Base) :
    0 < circularFlatBump c r p ↔ circularRadiusSquared c p < r^2 := by
  constructor
  · intro hp
    apply lt_of_not_ge
    intro hge
    exact (ne_of_gt hp) ((circularFlatBump_zero_iff c r p).mpr hge)
  · intro hp
    exact expNegInvGlue.pos_of_pos (sub_pos.mpr hp)

lemma circularRadiusSquared_le_norm {c p : Base} {r : ℝ}
    (hp : circularRadiusSquared c p ≤ r^2) : ‖p-c‖ ≤ |r| := by
  have h₁ : |p.1-c.1| ≤ |r| := by
    apply sq_le_sq.mp
    unfold circularRadiusSquared at hp
    nlinarith [sq_nonneg (p.2-c.2)]
  have h₂ : |p.2-c.2| ≤ |r| := by
    apply sq_le_sq.mp
    unfold circularRadiusSquared at hp
    nlinarith [sq_nonneg (p.1-c.1)]
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, Real.norm_eq_abs, max_le_iff]
    using And.intro h₁ h₂

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CircularSmoothingAtlas
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite smoothing atlas whose positive loci are actual coordinate disks.
The cutoffs are flat circular functions, not arbitrary subordinate bumps. -/
noncomputable section
open Set Manifold Filter
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

lemma circularCoordinateRegion_compact (p : M) (r : ℝ) :
    IsCompact (circularCoordinateRegion p r) := by
  apply (isCompact_closedBall (coordinateChart p p) |r|).of_isClosed_subset
    (isClosed_le (circularRadiusSquared_smooth _).continuous continuous_const)
  intro x hx
  rw [Metric.mem_closedBall,dist_eq_norm]
  exact circularRadiusSquared_le_norm hx

lemma circularManifoldBump_nonneg (p x : M) (r : ℝ) :
    0 ≤ circularManifoldBump p r x := by
  classical
  by_cases hx : x ∈ (coordinateChart p).source
  · rw [circularManifoldBump,indicator_of_mem hx]
    exact circularFlatBump_nonneg _ _ _
  · rw [circularManifoldBump,indicator_of_notMem hx]

lemma circularManifoldBump_pos_iff (p x : M) (r : ℝ) :
    0 < circularManifoldBump p r x ↔ x ∈ circularCoordinateDisk p r := by
  classical
  by_cases hx : x ∈ (coordinateChart p).source
  · simp only [circularManifoldBump,indicator_of_mem hx,circularCoordinateDisk,
      mem_inter_iff,hx,true_and,mem_preimage,Set.mem_ofPred_eq,circularFlatBump_pos_iff]
  · simp only [circularManifoldBump,indicator_of_notMem hx,circularCoordinateDisk,
      mem_inter_iff,hx,false_and,lt_self_iff_false]

variable [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma circularCoordinateDisk_open (p : M) (r : ℝ) :
    IsOpen (circularCoordinateDisk p r) := by
  exact (coordinateChart p).continuousOn.isOpen_inter_preimage
    (coordinateChart p).open_source
    (isOpen_lt (circularRadiusSquared_smooth _).continuous continuous_const)

omit [IsManifold planeModel ∞ M] in
lemma mem_circularCoordinateDisk (p : M) {r : ℝ} (hr : 0 < r) :
    p ∈ circularCoordinateDisk p r := by
  refine ⟨?_,?_⟩
  · rw [coordinateChart_source]
    exact mem_chart_source Plane p
  · change circularRadiusSquared (coordinateChart p p) (coordinateChart p p) < r^2
    simpa only [circularRadiusSquared,sub_self,zero_pow (by decide : 2 ≠ 0),zero_add] using
      sq_pos_of_pos hr

variable [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_compact (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsCompact (circularDiskClosure p r) :=
  (circularCoordinateRegion_compact p r).image_of_continuousOn
    ((coordinateChart p).continuousOn_symm.mono hregion)

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_source (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    circularDiskClosure p r ⊆ (coordinateChart p).source := by
  rintro x ⟨y,hy,rfl⟩
  exact (coordinateChart p).map_target (hregion hy)

lemma circularManifoldBump_smooth_support (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (circularManifoldBump p r) ∧
      tsupport (circularManifoldBump p r) ⊆ circularDiskClosure p r := by
  apply contMDiff_indicator_of_support (coordinateChart p).open_source
    (circularDiskClosure_compact p r hregion).isClosed
    (circularDiskClosure_source p r hregion)
    ((circularFlatBump_smooth _ r).contMDiff.comp_contMDiffOn (coordinateChart_smoothOn p))
  intro x hx hnot
  apply (circularFlatBump_zero_iff _ r _).mpr
  by_contra hlt
  apply hnot
  refine ⟨coordinateChart p x,?_,(coordinateChart p).left_inv hx⟩
  exact (not_le.mp hlt).le

omit [IsManifold planeModel ∞ M] [T2Space M] in
/-- The disks can be chosen inside any given neighborhood of their centers. -/
lemma exists_circularCoordinateDisk_subordinate (p : M) {V : Set M}
    (hV : IsOpen V) (hpV : p ∈ V) :
    ∃ r : ℝ, 0 < r ∧
      circularCoordinateRegion p r ⊆ (coordinateChart p).target ∧
      circularDiskClosure p r ⊆ V := by
  let e := coordinateChart p
  have hpS : p ∈ e.source := by rw [coordinateChart_source]; exact mem_chart_source Plane p
  have hU : IsOpen (e.target ∩ e.symm ⁻¹' V) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target hV
  have hc : e p ∈ e.target ∩ e.symm ⁻¹' V :=
    ⟨e.map_source hpS,by simpa only [mem_preimage,e.left_inv hpS] using hpV⟩
  obtain ⟨eps,heps,hball⟩ := Metric.isOpen_iff.mp hU (e p) hc
  have hsmall : ∀ x ∈ circularCoordinateRegion p (eps/2),
      x ∈ e.target ∩ e.symm ⁻¹' V := by
    intro x hx
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    have hb := circularRadiusSquared_le_norm hx
    rw [abs_of_pos (half_pos heps)] at hb
    exact hb.trans_lt (by linarith)
  refine ⟨eps/2,half_pos heps,fun x hx => (hsmall x hx).1,?_⟩
  rintro x ⟨y,hy,rfl⟩
  exact (hsmall y hy).2

variable [CompactSpace M]

/-- A finite collection of actual circular coordinate disks covers the
surface. Its flat cutoffs are smooth and subordinate to the given cover. -/
theorem exists_finite_circular_cutoffs (V : M → Set M)
    (hV : ∀ p, IsOpen (V p)) (hpV : ∀ p, p ∈ V p) :
    ∃ (t : Finset M) (r : t → ℝ),
      (∀ i : t, 0 < r i) ∧
      (∀ i : t, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target) ∧
      (∀ i : t, circularDiskClosure (i : M) (r i) ⊆ V i) ∧
      (∀ x : M, ∃ i : t, x ∈ circularCoordinateDisk (i : M) (r i)) ∧
      (∀ i : t, ContMDiff planeModel 𝓘(ℝ) ∞ (circularManifoldBump (i : M) (r i))) ∧
      (∀ i : t, tsupport (circularManifoldBump (i : M) (r i)) ⊆ V i) := by
  classical
  choose r hr ht hv using fun p => exists_circularCoordinateDisk_subordinate p (hV p) (hpV p)
  have hc : (univ : Set M) ⊆ ⋃ p, circularCoordinateDisk p (r p) := by
    intro p _
    exact mem_iUnion.mpr ⟨p,mem_circularCoordinateDisk p (hr p)⟩
  obtain ⟨t,hcover⟩ := isCompact_univ.elim_finite_subcover
    (fun p => circularCoordinateDisk p (r p))
    (fun p => circularCoordinateDisk_open p (r p)) hc
  refine ⟨t,fun i => r i,fun i => hr i,fun i => ht i,fun i => hv i,?_,?_,?_⟩
  · intro x
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hcover (mem_univ x))
    exact ⟨⟨i,hi⟩,hxi⟩
  · intro i
    exact (circularManifoldBump_smooth_support (i : M) (r i) (ht i)).1
  · intro i
    exact (circularManifoldBump_smooth_support (i : M) (r i) (ht i)).2.trans (hv i)

omit [IsManifold planeModel ∞ M] [T2Space M] [CompactSpace M] in
theorem normalize_finite_positive_cutoffs {ι : Type*} [Fintype ι]
    (f : ι → M → ℝ) (hf : ∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (f i))
    (hnon : ∀ i x, 0 ≤ f i x) (hcover : ∀ x, ∃ i, 0 < f i x) :
    ∃ w : ι → M → ℝ,
      (∀ i, ContMDiff planeModel 𝓘(ℝ) ∞ (w i)) ∧
      (∀ i x, 0 ≤ w i x) ∧ (∀ i x, 0 < w i x ↔ 0 < f i x) ∧
      (∀ i, tsupport (w i) = tsupport (f i)) ∧
      ∀ x, ∑ i, (w i x)^2 = 1 := by
  classical
  let sigma : M → ℝ := fun x => ∑ i, (f i x)^2
  have hpos (x : M) : 0 < sigma x := by
    obtain ⟨i,hi⟩ := hcover x
    exact (sq_pos_of_pos hi).trans_le
      (Finset.single_le_sum (fun j _ => sq_nonneg (f j x)) (Finset.mem_univ i))
  have hsigma : ContMDiff planeModel 𝓘(ℝ) ∞ sigma :=
    contMDiff_finsetSum (fun i _ => (hf i).pow 2)
  have hsqrt : ContMDiff planeModel 𝓘(ℝ) ∞ (fun x => Real.sqrt (sigma x)) := by
    intro x
    exact (Real.contDiffAt_sqrt (hpos x).ne').contMDiffAt.comp x (hsigma x)
  let w : ι → M → ℝ := fun i x => f i x / Real.sqrt (sigma x)
  have hwpos (i : ι) (x : M) : 0 < w i x ↔ 0 < f i x :=
    div_pos_iff_of_pos_right (Real.sqrt_pos.mpr (hpos x))
  refine ⟨w,fun i => (hf i).div₀ hsqrt (fun x => (Real.sqrt_pos.mpr (hpos x)).ne'),
    fun i x => div_nonneg (hnon i x) (Real.sqrt_nonneg _),hwpos,?_,?_⟩
  · intro i
    change closure (Function.support (w i)) = closure (Function.support (f i))
    congr 1
    ext x
    change w i x ≠ 0 ↔ f i x ≠ 0
    change f i x / Real.sqrt (sigma x) ≠ 0 ↔ f i x ≠ 0
    rw [div_ne_zero_iff]
    exact and_iff_left (Real.sqrt_pos.mpr (hpos x)).ne'
  · intro x
    calc
      ∑ i, (w i x)^2 = (∑ i, (f i x)^2) / (Real.sqrt (sigma x))^2 := by
        simp only [w,div_pow,Finset.sum_div]
      _ = sigma x / sigma x := by rw [Real.sq_sqrt (hpos x).le]
      _ = 1 := div_self (hpos x).ne'

/-- A finite atlas with circular positive loci. Outer cutoffs are identically
one near their supports, and all data stay inside the prescribed neighborhoods. -/
theorem exists_circular_smoothingAtlas (V : M → Set M)
    (hV : ∀ p, IsOpen (V p)) (hpV : ∀ p, p ∈ V p) :
    ∃ (A : SmoothingAtlas M) (r : A.centers → ℝ),
      (∀ i : A.centers, 0 < r i) ∧
      (∀ i : A.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target) ∧
      (∀ i : A.centers, circularDiskClosure (i : M) (r i) ⊆ V i) ∧
      (∀ i x, 0 ≤ A.weight i x) ∧
      (∀ i x, 0 < A.weight i x ↔ x ∈ circularCoordinateDisk (i : M) (r i)) ∧
      (∀ i, tsupport (A.weight i) ⊆ V i) ∧
      ∀ i x, x ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 x] (fun _ => 1) := by
  classical
  obtain ⟨t,r,hr,hregion,hinside,hcover,hsmooth,hsupport⟩ :=
    exists_finite_circular_cutoffs V hV hpV
  let f : t → M → ℝ := fun i => circularManifoldBump (i : M) (r i)
  obtain ⟨w,hw,hwnon,hwpos,hwsupport,hpart⟩ := normalize_finite_positive_cutoffs f hsmooth
    (fun i x => circularManifoldBump_nonneg (i : M) x (r i)) (fun x => by
      obtain ⟨i,hi⟩ := hcover x
      exact ⟨i,(circularManifoldBump_pos_iff (i : M) x (r i)).mpr hi⟩)
  have hwchart (i : t) : tsupport (w i) ⊆ (chart (i : M)).source := by
    rw [hwsupport i]
    intro x hx
    have hxC := (circularManifoldBump_smooth_support (i : M) (r i) (hregion i)).2 hx
    have hxS := circularDiskClosure_source (i : M) (r i) (hregion i) hxC
    simpa only [coordinateChart_source,chart_source] using hxS
  have hwV (i : t) : tsupport (w i) ⊆ V i := by
    rw [hwsupport i]
    exact hsupport i
  have hout : ∀ i : t, ∃ chi : M → ℝ,
      ContMDiff planeModel 𝓘(ℝ) ∞ chi ∧
      tsupport chi ⊆ (chart (i : M)).source ∧
      ∀ x ∈ tsupport (w i), chi =ᶠ[𝓝 x] (fun _ => 1) := by
    intro i
    have hc : IsCompact (tsupport (w i)) := (isClosed_tsupport _).isCompact
    obtain ⟨B,hB,hKB,hBc⟩ := hc.exists_isOpen_closure_subset
      ((chart (i : M)).open_source.mem_nhdsSet.mpr (hwchart i))
    obtain ⟨O,hO,hKO,hOc⟩ := hc.exists_isOpen_closure_subset (hB.mem_nhdsSet.mpr hKB)
    obtain ⟨chi,hchi,_,hchis,hchione⟩ :=
      exists_contMDiff_support_eq_eq_one_iff (I := planeModel) (n := (⊤ : ℕ∞))
        hB isClosed_closure hOc
    refine ⟨chi,hchi,?_,?_⟩
    · change closure (Function.support chi) ⊆ _
      rw [hchis]
      exact hBc
    · intro x hx
      filter_upwards [hO.mem_nhds (hKO hx)] with y hy
      exact (hchione y).mp (subset_closure hy)
  choose chi hchi hchis hchione using hout
  let A : SmoothingAtlas M :=
    ⟨t,w,chi,hw,hwchart,hchi,hchis,fun i x hx => (hchione i x hx).eq_of_nhds,hpart⟩
  refine ⟨A,r,hr,hregion,hinside,hwnon,?_,hwV,hchione⟩
  intro i x
  exact (hwpos i x).trans (circularManifoldBump_pos_iff (i : M) x (r i))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformCircularPhaseCharts
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Phase charts for entire circular patches, chosen with a radius uniform
in the center and in a compact family of nonzero linear phase parameters. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SurfaceJetCoordinates SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem uniform_circular_phase_charts {P : Set Base} (hP : IsCompact P)
    (hP0 : ∀ ell ∈ P, ell ≠ 0) {L : ℝ} (hL : 0 < L) :
    ∃ R : ℝ, 0 < R ∧ ∀ (q : M) (ell : Base), ell ∈ P →
      ∃ e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base,
        ContDiff ℝ ∞ e ∧ ContDiff ℝ ∞ e.symm ∧
        (∀ x, (baseEquiv (e x)).1 = centeredConvexPhase ell L (coordinateChart q q) (baseEquiv x)) ∧
        ∀ r : ℝ, 0 ≤ r → r ≤ R → ∀ x ∈ circularCoordinateRegion q r,
          baseEquiv.symm x ∈ e.source := by
  obtain ⟨R,hR,hcharts⟩ := compact_uniform_centered_charts hP hP0 hL
  refine ⟨R,hR,?_⟩
  intro q ell hell
  obtain ⟨e,hphase,he,hi,hcover⟩ := hcharts ell hell (coordinateChart q q)
  refine ⟨jetPhaseChart e,jetPhaseChart_smooth he,jetPhaseChart_symm_smooth hi,?_,?_⟩
  · intro x
    rw [jetPhaseChart_apply,baseEquiv.apply_symm_apply,hphase]
  · intro r hr hrR x hx
    rw [jetPhaseChart_source]
    change baseEquiv (baseEquiv.symm x) ∈ e.source
    rw [baseEquiv.apply_symm_apply]
    apply hcover
    rw [Metric.mem_closedBall,dist_eq_norm]
    exact (circularRadiusSquared_le_norm hx).trans (by simpa only [abs_of_nonneg hr] using hrR)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseParameterBalls
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact independent parameter balls about the three nonzero covectors. -/
noncomputable section
open Set Metric
open scoped Topology
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes

theorem phase_parameter_balls (P : PhaseBasis) :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 ∧
      ∀ j : Fin 3, IsCompact (closedBall (P.ξ j) eps) ∧
        ∀ ell ∈ closedBall (P.ξ j) eps, ell ≠ 0 ∧ ‖ell‖ ≤ ‖P.ξ‖+1 := by
  let eps := min 1 (min (‖P.ξ 0‖/2) (min (‖P.ξ 1‖/2) (‖P.ξ 2‖/2)))
  have h0 : 0 < ‖P.ξ 0‖ := norm_pos_iff.mpr (P.nonzero 0)
  have h1 : 0 < ‖P.ξ 1‖ := norm_pos_iff.mpr (P.nonzero 1)
  have h2 : 0 < ‖P.ξ 2‖ := norm_pos_iff.mpr (P.nonzero 2)
  have heps : 0 < eps := lt_min zero_lt_one (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have heps1 : eps ≤ 1 := min_le_left _ _
  have hs (j : Fin 3) : eps < ‖P.ξ j‖ := by
    have ha := (min_le_right 1 (min (‖P.ξ 0‖/2) (min (‖P.ξ 1‖/2) (‖P.ξ 2‖/2))))
    have hb := min_le_left (‖P.ξ 0‖/2) (min (‖P.ξ 1‖/2) (‖P.ξ 2‖/2))
    have hc := min_le_right (‖P.ξ 0‖/2) (min (‖P.ξ 1‖/2) (‖P.ξ 2‖/2))
    have hd := min_le_left (‖P.ξ 1‖/2) (‖P.ξ 2‖/2)
    have he := min_le_right (‖P.ξ 1‖/2) (‖P.ξ 2‖/2)
    fin_cases j
    · change eps < ‖P.ξ 0‖
      dsimp only [eps]
      linarith
    · change eps < ‖P.ξ 1‖
      dsimp only [eps]
      linarith
    · change eps < ‖P.ξ 2‖
      dsimp only [eps]
      linarith
  refine ⟨eps,heps,heps1,fun j => ⟨isCompact_closedBall _ _,?_⟩⟩
  intro ell hell
  have hb : ‖ell-P.ξ j‖ ≤ eps := by simpa only [mem_closedBall,dist_eq_norm] using hell
  refine ⟨?_,?_⟩
  · intro hz
    rw [hz,zero_sub,norm_neg] at hb
    exact (not_le_of_gt (hs j)) hb
  · calc
      ‖ell‖ ≤ ‖ell-P.ξ j‖+‖P.ξ j‖ := by simpa only [sub_add_cancel] using norm_add_le (ell-P.ξ j) (P.ξ j)
      _ ≤ eps+‖P.ξ‖ := add_le_add hb (norm_le_pi_norm P.ξ j)
      _ ≤ ‖P.ξ‖+1 := by linarith

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PerturbedCircularCutoffs
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual independent radius perturbations of circular manifold cutoffs.
A fixed larger disk supplies common support and uniform continuity. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularCoordinateRegion_mono (p : M) {r R : ℝ} (h : r^2 ≤ R^2) :
    circularCoordinateRegion p r ⊆ circularCoordinateRegion p R := by
  intro x hx
  exact hx.trans h

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ShrinkingCircularWeight
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weight-preserving independent disk shrinkage. The quotient is only
used where the original bump is positive; the smaller compact support
makes the resulting weight globally smooth. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_subset_disk (p : M) {r R : ℝ} (h : r^2 < R^2)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    circularDiskClosure p r ⊆ circularCoordinateDisk p R := by
  rintro x ⟨y,hy,rfl⟩
  refine ⟨(coordinateChart p).map_target (hreg hy),?_⟩
  change circularRadiusSquared (coordinateChart p p)
    (coordinateChart p ((coordinateChart p).symm y)) < R^2
  rw [(coordinateChart p).right_inv (hreg hy)]
  exact hy.trans_lt h

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma shrinkingCircularWeight_support (p : M) (w : M → ℝ) (r0 r : ℝ) :
    tsupport (shrinkingCircularWeight p w r0 r) ⊆ tsupport (circularManifoldBump p r) := by
  apply closure_mono
  intro x hx
  contrapose! hx
  simp only [Function.mem_support,not_not] at hx ⊢
  simp only [shrinkingCircularWeight,hx,zero_div,mul_zero]

/-- Every strictly smaller radius gives a globally smooth actual weight,
with support in the smaller closed disk. -/
theorem shrinkingCircularWeight_smooth (p : M) (w : M → ℝ)
    (hw : ContMDiff planeModel 𝓘(ℝ) ∞ w) {r0 r : ℝ}
    (hreg0 : circularCoordinateRegion p r0 ⊆ (coordinateChart p).target)
    (hr : r^2 < r0^2) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (shrinkingCircularWeight p w r0 r) ∧
      tsupport (shrinkingCircularWeight p w r0 r) ⊆ circularDiskClosure p r := by
  have hreg := (circularCoordinateRegion_mono p hr.le).trans hreg0
  have hb := circularManifoldBump_smooth_support p r hreg
  have hb0 := circularManifoldBump_smooth_support p r0 hreg0
  have hs := (shrinkingCircularWeight_support p w r0 r).trans hb.2
  refine ⟨?_,hs⟩
  apply contMDiff_of_tsupport
  intro x hx
  have hd := (circularDiskClosure_subset_disk p hr hreg) (hs hx)
  have hp := (circularManifoldBump_pos_iff p x r0).mpr hd
  exact (hw x).mul ((hb.1 x).div₀ (hb0.1 x) hp.ne')

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShortMetricPath
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The positive metric remainder and the actual smooth metric path used
by the finite primitive preparation. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathDualAdd
local instance pathFiberNormed_r47b1a3_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance pathFiberSpace_r47b1a3_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance pathDualSmul_r47b1a3_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M) (g : SmoothMetric M) {F : M → Space}
  (hF : ContMDiff planeModel spaceModel ∞ F)
  (hshort : ∀ p v, inducedForm F p v v ≤ (1/2 : ℝ)*g.inner p v v)

local instance pathSectionNormed_r47b1a3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance pathSectionSpace_r47b1a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma shortPathMetric_apply (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
    (s : ℝ) (hs : 0 ≤ s) (p : M) (v w : TangentSpace planeModel p) :
    (A.shortPathMetric g hF hshort hI s hs).inner p v w =
      (1-s)*inducedForm F p v w+s*g.inner p v w := by
  change inducedForm F p v w+s*(g.inner p v w-inducedForm F p v w) = _
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformMetricPathBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-order metric bounds fixed before finite spherical modifications. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberSpace
local instance pathBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.pathBoundFiberSpace
local instance pathBoundSectionNormed_r47b1a3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance pathBoundSectionSpace_r47b1a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma exists_tensorWeighted_bound (m : ℕ) {T : ∀ p : M, CovariantTwoTensor p}
    (hT : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (T p))) :
    ∃ C : ℝ, 0 ≤ C ∧ A.TensorWeightedBound 1 m C T := by
  classical
  choose C hC hb using fun i : A.centers => compact_smooth_bound
    (A.bundleLocalize_smooth A.tensorTriv A.tensorTriv_domain i hT)
    (localize_compact (i : M) (A.weight_support i) (A.bundleComponent A.tensorTriv i T)) m
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => hC i), fun i => ?_⟩
  exact (hb i).mono_const (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))

lemma uniform_induced_tensor_bound {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ F : M → Space, ContMDiff planeModel spaceModel ∞ F →
      A.WeightedBound 1 (m+1) C F → A.TensorWeightedBound 1 m D (inducedTensor F) := by
  obtain ⟨D,hD,hbound⟩ := A.global_cubic_remainder_bound m 0 C le_rfl hC
  refine ⟨D,hD,fun F hF hb => ?_⟩
  have hz : A.WeightedBound 1 (m+1) (0*(1*1)) (0 : M → Space) := by
    intro i
    simp only [zero_mul]
    change WeightedEstimates.WeightedBound univ 1 (m+1) 0 (localize (i : M) (A.weight i) 0)
    have he : localize (i : M) (A.weight i) (0 : M → Space) = 0 := by
      funext x
      by_cases hx : x ∈ (chart (i : M)).target <;> simp [localize,hx]
    rw [he]
    exact weightedBound_zero univ 1 (m+1)
  have ht := hbound 1 1 zero_lt_one le_rfl zero_le_one le_rfl 0 F
    contMDiff_const hF hz (by simpa only [one_pow,mul_one] using hb)
  have he : linearMetricTensor (0 : M → Space) F = 0 := by
    funext p
    ext v w
    change inner ℝ (show Space from mfderiv planeModel spaceModel (0 : M → Space) p v)
        (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        (show Space from mfderiv planeModel spaceModel (0 : M → Space) p w) = 0
    have hd : (mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p :
        TangentSpace planeModel p →L[ℝ] Space) = 0 := mfderiv_const
    change inner ℝ ((mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p) v)
        (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v)
        ((mfderiv planeModel spaceModel (fun _ : M => (0 : Space)) p) w) = 0
    rw [hd]
    change inner ℝ (0 : Space) (show Space from mfderiv planeModel spaceModel F p w) +
      inner ℝ (show Space from mfderiv planeModel spaceModel F p v) (0 : Space) = 0
    rw [inner_zero_left,inner_zero_right,add_zero]
  simpa only [he,zero_add,one_pow,div_one,mul_one] using ht

lemma uniform_short_path_tensor_bound (g : SmoothMetric M) {C : ℝ} (hC : 0 ≤ C)
    (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      (hI : ∀ p, Function.Injective (mfderiv planeModel spaceModel F p))
      (hshort : ∀ p v, inducedForm F p v v ≤ (1/2 : ℝ)*g.inner p v v),
      A.WeightedBound 1 (m+1) C F → ∀ s : ℝ, ∀ hs : 0 ≤ s, s ≤ 1 →
      A.TensorWeightedBound 1 m D (A.shortPathMetric g hF hshort hI s hs).inner := by
  obtain ⟨D,hD,hb⟩ := A.uniform_induced_tensor_bound hC m
  obtain ⟨E,hE,he⟩ := A.exists_tensorWeighted_bound m g.contMDiff
  refine ⟨D+E,add_nonneg hD hE,?_⟩
  intro F hF hI hshort hFC s hs hs1
  have hleft := A.tensorWeightedBound_const_smul (A.inducedTensor_smooth hF) (hb F hF hFC) (1-s)
  have hright := A.tensorWeightedBound_const_smul g.contMDiff he s
  have hsum := A.tensorWeightedBound_add (A.inducedTensor_smooth hF).const_smul_section
    g.contMDiff.const_smul_section zero_le_one hleft hright
  have hid : (A.shortPathMetric g hF hshort hI s hs).inner =
      (1-s) • inducedTensor F+s • g.inner := by
    funext p
    ext v w
    exact A.shortPathMetric_apply g hF hshort hI s hs p v w
  rw [hid]
  intro i
  apply (hsum i).mono_const
  rw [abs_of_nonneg (sub_nonneg.mpr hs1),abs_of_nonneg hs]
  nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_UniformConvexCircularAtlas
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A circular cover selected after local phase convexity has been fixed.
All metric bounds are measured in the original, independent atlas. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

omit [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] in
lemma circular_radius_le_of_subordinate (p : M) {r R : ℝ} (hr : 0 < r)
    (hreg : circularCoordinateRegion p r ⊆ (coordinateChart p).target)
    (hsmall : ∀ q ∈ circularDiskClosure p r,
      ‖coordinateChart p q-coordinateChart p p‖ < R) : r ≤ R := by
  let x : Base := ((coordinateChart p p).1+r,(coordinateChart p p).2)
  have hx : x ∈ circularCoordinateRegion p r := by
    change circularRadiusSquared (coordinateChart p p) x ≤ r^2
    dsimp [x,circularRadiusSquared]
    ring_nf
    exact le_refl _
  have hh := hsmall ((coordinateChart p).symm x) ⟨x,hx,rfl⟩
  rw [(coordinateChart p).right_inv (hreg hx)] at hh
  have he : x-coordinateChart p p = (r,0) := by ext <;> simp [x]
  rw [he,Prod.norm_def] at hh
  simpa only [Real.norm_eq_abs,abs_of_pos hr,norm_zero,max_eq_left hr.le] using hh.le

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_convex_circular_atlas (g : SmoothMetric M) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) (K : M → ℝ) (hK : ∀ p, 0 ≤ K p) :
    ∃ L : M → ℝ, (∀ p, 0 < L p) ∧
      ∀ R : M → ℝ, (∀ p, 0 < R p) →
      ∀ V : M → Set M, (∀ p, IsOpen (V p)) → (∀ p, p ∈ V p) →
      ∃ (B : SmoothingAtlas M) (r : B.centers → ℝ),
        (∀ i : B.centers, 0 < r i ∧ r i ≤ R (i : M)) ∧
        (∀ i : B.centers, circularDiskClosure (i : M) (r i) ⊆ V i) ∧
        (∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target) ∧
        (∀ i p, 0 ≤ B.weight i p) ∧
        (∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i)) ∧
        (∀ i p, p ∈ tsupport (B.weight i) → B.outer i =ᶠ[𝓝 p] (fun _ => 1)) ∧
        ∀ h : SmoothMetric M, A.TensorWeightedBound 1 1 C h.inner →
          (∀ q v, c*g.inner q v v ≤ h.inner q v v) →
          ∀ (i : B.centers) (q : M), q ∈ circularDiskClosure (i : M) (r i) →
            ∀ ell : Base, ‖ell‖ ≤ K i → ∀ v : Base,
              (L i/2)*(v.1^2+v.2^2) ≤ coordinateMetricHessian (coordinateMetric h (i : M))
                (centeredConvexPhase ell (L i) (coordinateChart (i : M) (i : M)))
                (coordinateChart (i : M) q) v v := by
  classical
  choose L U hL hU hpU hUs hconvex using fun p =>
    A.local_uniform_convexity g hc hC (hK p) p
  refine ⟨L,hL,?_⟩
  intro R hR V hV hpV
  let W : M → Set M := fun p => (U p ∩ V p) ∩ ((coordinateChart p).source ∩
    (coordinateChart p) ⁻¹' Metric.ball (coordinateChart p p) (R p))
  have hW (p : M) : IsOpen (W p) :=
    ((hU p).inter (hV p)).inter ((coordinateChart p).isOpen_inter_preimage Metric.isOpen_ball)
  have hpW (p : M) : p ∈ W p := by
    refine ⟨⟨hpU p,hpV p⟩,?_,Metric.mem_ball_self (hR p)⟩
    rw [coordinateChart_source]; exact mem_chart_source Plane p
  obtain ⟨B,r,hr,hreg,hinside,hwnon,hwpos,_hsupp,houter⟩ :=
    exists_circular_smoothingAtlas W hW hpW
  refine ⟨B,r,fun i => ⟨hr i,?_⟩,(fun i p hp => (hinside i hp).1.2),hreg,hwnon,hwpos,houter,?_⟩
  · apply circular_radius_le_of_subordinate (i : M) (hr i) (hreg i)
    intro q hq
    have hh : coordinateChart (i : M) q ∈ Metric.ball (coordinateChart (i : M) (i : M)) (R (i : M)) :=
      (hinside i hq).2.2
    simpa only [Metric.mem_ball,dist_eq_norm] using hh
  · intro h hb hlower i q hq ell hell v
    exact hconvex i h hb hlower q (hinside i hq).1.1 ell hell v

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ReferenceCircularAtlas
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A reference circular atlas with positive coefficient forms and convex
phases, chosen before the number of cycles or generic perturbations. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry SurfaceJetCoordinates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem exists_reference_circular_atlas (gref g : SmoothMetric M) {c C : ℝ}
    (hc : 0 < c) (hC : 0 ≤ C) : Nonempty (ReferenceCircularAtlas A gref g c C) := by
  classical
  choose P hP using fun p : M => positive_tensor_has_basis
    (coordinateMetric_positive_center gref p).1 (coordinateMetric_positive_center gref p).2
  choose eps heps heps1 hparams using fun p => phase_parameter_balls (P p)
  obtain ⟨L,hL,hchoose⟩ := A.uniform_convex_circular_atlas g hc hC
    (fun p => ‖(P p).ξ‖+1) (fun _ => by positivity)
  choose R hR hcharts using fun (p : M) (j : Fin 3) =>
    uniform_circular_phase_charts (M := M) (isCompact_closedBall ((P p).ξ j) (eps p))
      (fun ell hell => ((hparams p j).2 ell hell).1) (hL p)
  let R₀ : M → ℝ := fun p => min (R p 0) (min (R p 1) (R p 2))
  have hR₀ (p : M) : 0 < R₀ p := lt_min (hR p 0) (lt_min (hR p 1) (hR p 2))
  have hRle (p : M) (j : Fin 3) : R₀ p ≤ R p j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  choose U hU hpU hUs hgood using fun p => local_reference_phase_basis gref p (P p) (hP p) (L p)
  obtain ⟨B,r,hr,hinside,hreg,hnon,hpos,houter,hconvex⟩ := hchoose R₀ hR₀ U hU hpU
  refine ⟨{
    B := B, P := fun i => P i, L := fun i => L i,
    radius := r, epsilon := fun i => eps i,
    L_pos := fun i => hL i, radius_pos := fun i => (hr i).1,
    epsilon_pos := fun i => heps i, region := hreg,
    weight_nonneg := hnon, weight_positive := hpos, outer := houter,
    parameters := fun i j ell hell => (hparams i j).2 ell hell,
    admissible := fun i p hp => (hgood i p (hinside i hp)).1,
    positive := fun i p hp => (hgood i p (hinside i hp)).2,
    convex := hconvex,
    charts := ?_ }⟩
  intro i j ell hell
  obtain ⟨e,he,hei,heq,hcover⟩ := hcharts (i : M) j (i : M) ell hell
  exact ⟨e,he,hei,heq,hcover (r i) (hr i).1.le ((hr i).2.trans (hRle i j))⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformScaledPathBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual straight metric path has one budget for the whole fixed
scaled starting family, before choosing any finite crossing set. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_scaled_path_bound (g : SmoothMetric M) (r : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G → A.WeightedBound 1 2 D G →
      (∀ p, Function.Injective (mfderiv planeModel spaceModel (r • G) p)) →
      (∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v) →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      A.TensorWeightedBound 1 1 C
        (inducedTensor (r • G)+s • (g.inner-inducedTensor (r • G))) := by
  obtain ⟨C,hC,hbound⟩ := A.uniform_short_path_tensor_bound g (mul_nonneg (abs_nonneg r) hD) 1
  refine ⟨C,hC,?_⟩
  intro G hG hb hI hshort s hs hs1
  have hscaled := space_smul_contMDiff hG r
  have hgb := A.weightedBound_const_smul hG hb r
  have hh := hbound (r • G) hscaled hI hshort hgb s hs hs1
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ConditionalMain
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth isometric immersions constructed from spherical immersions,
and from the compact surface case of Whitney (1944), Theorem 8, p.274. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]
local instance mainFiberNormed_r47b1a3_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance mainFiberSpace_r47b1a3_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance mainDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

local instance mainDualSmul_r47b1a3_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance mainSectionNormed_r47b1a3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance mainSectionSpace_r47b1a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [SecondCountableTopology M] in
/-- The construction starting from a smooth unit spherical immersion. All
primitive amplitudes and the starting scale are chosen uniformly before
selecting the finite crossings. -/
theorem isometric_immersion_of_spherical_immersion_oai (g : SmoothMetric M)
    {I : M → Space} (hI : ContMDiff planeModel spaceModel ∞ I)
    (hunit : ∀ p, ‖I p‖ = 1)
    (hImm : ∀ p, Function.Injective (mfderiv planeModel spaceModel I p)) :
    ∃ W : M → Space, IsSmoothIsometricImmersion M g W := by
  classical
  obtain ⟨A⟩ := exists_smoothingAtlas (M := M)
  obtain ⟨r,D,c,hr,hr1,hD,hc,_hIb,_hIm,hIs,hstart⟩ :=
    A.reference_circular_starting_family g hI hunit hImm zero_lt_one
  let gref := A.shortRemainderMetric g (space_smul_contMDiff hI r) hIs
  have href : gref.inner = g.inner-inducedTensor (r • I) := rfl
  obtain ⟨C,hC,hpath⟩ := A.uniform_scaled_path_bound g r hD
  obtain ⟨d⟩ := A.exists_reference_circular_atlas gref g hc (show 0 ≤ C+1 by linarith)
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hterm⟩ := d.uniform_corrected_term_C1 hI r href hD
  let m := Fintype.card (d.B.centers × Fin 3)
  let e : Fin m ≃ (d.B.centers × Fin 3) := (Fintype.equivFin _).symm
  obtain ⟨mapTol,delta,W,hmapTol,hmapLe,_hdelta,_hdeltaR,hW,hcycles⟩ :=
    d.corrected_cycles hI r href hpt hwt hmt e
  obtain ⟨E,hE,hterms⟩ := hterm (W 1) (hW 1)
  obtain ⟨N,hN,hrealize⟩ := A.independent_circular_realization g c C d.B
    d.radius d.L (fun i => ‖(d.P i).ξ‖+1) d.L_pos d.region
    d.weight_nonneg d.weight_positive d.convex m E hE
  obtain ⟨q,hindex,houter,_hchart,hpart,hell,hphase,hweights,hweightClose,hcorrect⟩ :=
    hcycles N hN
  obtain ⟨G,g₀,normal,hG,_hu,hG₀,hg₀,⟨good⟩,_hn,hnear,hGb,hlower,_hgm,hshort,hgeom⟩ :=
    hstart (N*m) d.B q mapTol hmapTol
  obtain ⟨f,dCirc,hamp,hphi,hcurves,_hrad,_houter',_hchart',hlinear,hconvex,hcycle,hcyclePhase,_htotal⟩ :=
    hcorrect G hG hnear
  have hnear' : A.WeightedBound 1 1 mt (G-I) :=
    fun i => (hnear i).mono_const hmapLe
  have hcopy (k : Fin N) (b : d.B.centers × Fin 3) :
      (finProdFinEquiv (k,e.symm b)).divNat = k ∧
        e (finProdFinEquiv (k,e.symm b)).modNat = b := by
    have hh := Prod.mk.inj (finProdFinEquiv.symm_apply_apply (k,e.symm b))
    exact ⟨hh.1,by rw [hh.2,e.apply_symm_apply]⟩
  have hell' (k : Fin N) (i : d.B.centers) (j : Fin 3) :
      ‖d.cycleLinearParts e q k i j-(d.P i).ξ j‖ < pt := by
    have h := hphase (finProdFinEquiv (k,e.symm (i,j)))
    simpa only [ReferenceCircularAtlas.cycleLinearParts,
      (hcopy k (i,j)).2] using h
  have htermBound (k : Fin N) (a : Fin m) :
      A.TensorWeightedBound 1 1 E ((f k).term a) := by
    let f' := (f k).reindex e.symm
    have hp' : f'.phase = d.perturbedPhases (d.cycleLinearParts e q k) := by
      funext b
      exact (hphi k (e.symm b)).trans (congrArg _ (e.apply_symm_apply b))
    have ha' : f'.amplitude = d.B.correctedPrimitiveAmplitude d.basis
        (d.cycleWeights e q k) (d.perturbedPhases (d.cycleLinearParts e q k))
        (g.inner-inducedTensor (r • G)) := by
      funext b
      exact (hamp k (e.symm b)).trans (congrArg _ (e.apply_symm_apply b))
    have hnon (b : d.B.centers × Fin 3) :
        ContMDiff planeModel 𝓘(ℝ) ∞ (d.cycleWeights e q k b) := by
      let a : Fin (N*m) := finProdFinEquiv (k,e.symm b)
      have hh : e a.modNat = b := (hcopy k b).2
      have hrsmall : (q.radius a)^2 < (d.radius b.1)^2 := by
        have hrpos := q.radius_pos a
        have hro := q.radius_outer a
        rw [houter a,hh] at hro
        nlinarith [d.radius_pos b.1]
      exact (shrinkingCircularWeight_smooth (b.1 : M) (d.B.weight b.1)
        (d.B.weight_smooth b.1) (d.region b.1) hrsmall).1
    have hsupp (b : d.B.centers × Fin 3) :
        tsupport (d.cycleWeights e q k b) ⊆ tsupport (d.B.weight b.1) := by
      apply closure_mono
      intro p hp
      change d.cycleWeights e q k b p ≠ 0 at hp
      change d.B.weight b.1 p ≠ 0
      intro hz
      exact hp (by simp only [ReferenceCircularAtlas.cycleWeights,shrinkingCircularWeight,hz,zero_mul])
    have hb := hterms (d.cycleLinearParts e q k) (d.cycleWeights e q k) (hell' k)
      hnon hsupp (hweightClose k) (fun b => hweights k b 1) G hG hnear' hGb f' hp' ha' (e a)
    change A.TensorWeightedBound 1 1 E ((f k).term (e.symm (e a))) at hb
    simpa only [e.symm_apply_apply] using hb
  have hshort' : ∀ p v, inducedForm (r • G) p v v ≤ (1/2 : ℝ)*g.inner p v v := by
    intro p v
    change inducedTensor (r • G) p v v ≤ _
    rw [← hg₀]
    exact hshort p v
  have hpBound (k : Fin N) : A.TensorWeightedBound 1 1 C
      (g₀.inner+((k.val : ℝ)/(N : ℝ)) • (g.inner-inducedTensor (r • G))) := by
    rw [hg₀]
    exact hpath G hG hGb (hG₀.mfderiv_injective) hshort' _
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      ((div_le_one (by exact_mod_cast hN)).mpr (by exact_mod_cast k.isLt.le))
  have hcv (a : Fin (N*m)) : dCirc.convexPart a = d.L (dCirc.curves a).index := by
    rw [hconvex,hpart,hcurves,hindex]
  have hlin (a : Fin (N*m)) : ‖dCirc.linearPart a‖ ≤ ‖(d.P (dCirc.curves a).index).ξ‖+1 := by
    rw [hlinear,hcurves,hindex]
    exact hell a
  have htarget : g.inner = g₀.inner+(g.inner-inducedTensor (r • G)) := by
    rw [hg₀]
    abel
  have hgeom' : FiniteBoundaryGeometry dCirc.curves
      (boundaryCrossingSet dCirc.curves univ) (r • G) normal := by
    rw [hcurves]
    exact hgeom
  obtain ⟨F,hF,_hgood⟩ := hrealize g₀ hlower _ f htermBound hpBound dCirc
    hcycle hcyclePhase hcv hlin g htarget (r • G) normal hG₀ good hgeom'
  exact ⟨F,hF⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.isometric_immersion_of_spherical_immersion_oai.{u_1}
