-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:43:23.211203+00:00
-- url     : https://prove2.me/submissions/21c462e2-0c49-478f-9556-669b69fbd97c

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_QuadraticMean
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.QuadraticMean

lemma phase_add (θ ψ : ℝ) : phase (θ + ψ) = phase θ * phase ψ := by
  simp only [phase, ofReal_add, add_mul, Complex.exp_add]

lemma phase_conj (θ : ℝ) : star (phase θ) = phase (-θ) := by
  simp only [phase, Complex.star_def, ← Complex.exp_conj, map_mul, conj_ofReal, conj_I, ofReal_neg]
  congr 1
  ring

lemma phase_sub (θ ψ : ℝ) : phase (θ - ψ) = phase θ * star (phase ψ) := by
  rw [phase_conj, ← phase_add, sub_eq_add_neg]

lemma phase_zero : phase 0 = 1 := by simp [phase]

lemma real_product (a b : ℂ) : a.re * b.re = ((a * star b).re + (a * b).re) / 2 := by
  simp only [Complex.star_def, mul_re, conj_re, conj_im]
  ring

lemma mode_product (θ ψ : ℝ) (a b : ℂ) :
    (phase θ * a).re * (phase ψ * b).re =
      ((phase (θ - ψ) * (a * star b)).re + (phase (θ + ψ) * (a * b)).re) / 2 := by
  rw [real_product, phase_sub, phase_add]
  simp only [Complex.star_def, map_mul]
  congr 2 <;> congr 1 <;> ring



theorem realMode_dot {n : ℕ} (θ ψ : ℝ) (A B : CVec n) :
    realMode θ A ⬝ᵥ realMode ψ B =
      ((phase (θ - ψ) * (A ⬝ᵥ conjugate B)).re +
        (phase (θ + ψ) * (A ⬝ᵥ B)).re) / 2 := by
  unfold realMode realPart dotProduct conjugate
  simp only [Pi.smul_apply, smul_eq_mul, mode_product, Finset.mul_sum, Complex.re_sum]
  rw [← Finset.sum_div, Finset.sum_add_distrib]




theorem realMode_self_phase {n : ℕ} (θ : ℝ) (A B : CVec n) :
    realMode θ A ⬝ᵥ realMode θ B =
      (A ⬝ᵥ conjugate B).re / 2 + (phase (2 * θ) * (A ⬝ᵥ B)).re / 2 := by
  rw [realMode_dot, sub_self, phase_zero, one_mul]
  have h : θ + θ = 2 * θ := by ring
  rw [h, add_div]



lemma phase_comp_hasFDerivAt {φ : Base → ℝ} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (τ : ℝ) :
    HasFDerivAt (fun q => phase (φ q / τ))
      (phase (φ p / τ) • ((I / (τ : ℂ)) • (Complex.ofRealCLM.comp (fderiv ℝ φ p)))) p := by
  have h := ((Complex.ofRealCLM.hasFDerivAt.comp p hφ.hasFDerivAt).const_mul
    (I / (τ : ℂ))).cexp
  have he (q : Base) : phase (φ q / τ) = Complex.exp (I / (τ : ℂ) * (φ q : ℂ)) := by
    simp only [phase, ofReal_div]
    congr 1
    ring
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, he] using h

lemma derivative_displacement {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n} {p : Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (v : Base) :
    fderiv ℝ (displacement τ φ Z) p v =
      realMode (φ p / τ) (derivativeAmplitude τ φ Z v p) := by
  have hc := ((phase_comp_hasFDerivAt hφ τ).fun_smul hZ.hasFDerivAt)
  have hr := (realPartCLM n).hasFDerivAt.comp p hc
  simp only [Function.comp_def] at hr
  rw [show displacement τ φ Z = fun q => realPartCLM n (phase (φ q / τ) • Z q) from rfl,
    hr.fderiv]
  ext i
  simp only [realPartCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.pi_apply,
    Complex.reCLM_apply, ContinuousLinearMap.proj_apply, add_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    Complex.ofRealCLM_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    realMode, realPart, derivativeAmplitude]
  congr 1
  ring



end ClosedSurfaceR4.QuadraticMean

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_ForcedSolve
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseMean ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.QuadraticMean (displacement)
open Set Filter

lemma contDiffOn_displacement {n : ℕ} {U : Set Base} {φ : Base → ℝ} {Z : Field n}
    (hφ : ContDiffOn ℝ ∞ φ U) (hZ : ContDiffOn ℝ ∞ Z U) (τ : ℝ) :
    ContDiffOn ℝ ∞ (displacement τ φ Z) U := by
  have he : ContDiffOn ℝ ∞ (fun p => QuadraticMean.phase (φ p / τ)) U := by
    exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hφ.div_const τ)).mul contDiffOn_const).cexp
  exact (QuadraticMean.realPartCLM n).contDiff.comp_contDiffOn (he.smul hZ)



end ClosedSurfaceR4.RealModes

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ManifoldSmoothing
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual smoothing maps on a closed surface, assembled from a fixed atlas. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma restore_smooth (p : M) {χ : M → ℝ}
    (hχ : ContMDiff planeModel 𝓘(ℝ) ∞ χ)
    (hs : tsupport χ ⊆ (chart p).source) {h : Base → V} (hh : ContDiff ℝ ∞ h) :
    ContMDiff planeModel 𝓘(ℝ, V) ∞ (restore p χ h) := by
  apply (contMDiff_indicator_of_support (chart p).open_source
    (isClosed_tsupport χ) hs
    (hχ.contMDiffOn.smul (hh.contMDiff.comp_contMDiffOn (chart_smooth p))) ?_).1
  intro x _ hx
  change χ x • h (chart p x) = 0
  rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasRestore
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A displacement supported on an atlas weight's compact support is
restored exactly in that chart; the outer cutoff introduces no jet error. -/
noncomputable section
open Set
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Manifold
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma mem_weight_support_of_plane (i : A.centers) {p : M} (hp : p ∈ (chart (i : M)).source)
    (h : planeCoordinateIsometry (chart (i : M) p) ∈
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) : p ∈ tsupport (A.weight i) := by
  obtain ⟨y,hy,he⟩ := h
  have hyEq : y = chart (i : M) p := planeCoordinateIsometry.injective he
  subst y
  obtain ⟨q,hq,hqp⟩ := hy
  have hqEq : q = p := (chart (i : M)).injOn (A.weight_support i hq) hp hqp
  rwa [hqEq] at hq

lemma restore_plane_on_source (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) p =
      f (planeCoordinateIsometry (chart (i : M) p)) := by
  rw [restore,indicator_of_mem hp]
  change A.outer i p • f (planeCoordinateIsometry (chart (i : M) p)) = _
  by_cases hz : f (planeCoordinateIsometry (chart (i : M) p)) = 0
  · rw [hz,smul_zero]
  · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hf (subset_tsupport f hz))),one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Supported restoration commutes with all local derivatives, including
its actual manifold differential, and preserves the original atlas support. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restore_plane_tsupport (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    tsupport (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) ⊆
      tsupport (A.weight i) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro p hp
  by_cases hs : p ∈ (chart (i : M)).source
  · apply A.mem_weight_support_of_plane i hs
    apply hf
    apply subset_tsupport f
    intro hz
    apply hp
    rw [A.restore_plane_on_source i f hf hs,hz]
  · exfalso
    apply hp
    simp only [restore,indicator_of_notMem hs]

lemma restore_plane_mfderiv (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (hd : DifferentiableAt ℝ f (planeCoordinateIsometry (chart (i : M) p))) :
    mfderiv planeModel 𝓘(ℝ,V)
      (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p =
    (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
      (planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp
        (mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p)) := by
  have he : restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) =ᶠ[𝓝 p]
      (f ∘ planeCoordinateIsometry) ∘ chart (i : M) := by
    filter_upwards [(chart (i : M)).open_source.mem_nhds hp] with x hx
    exact A.restore_plane_on_source i f hf hx
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have hfc : DifferentiableAt ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p) :=
    hd.comp _ planeCoordinateIsometry.differentiableAt
  rw [he.mfderiv_eq]
  change mfderiv planeModel 𝓘(ℝ,V) ((f ∘ planeCoordinateIsometry) ∘ chart (i : M)) p = _
  rw [mfderiv_comp p hfc.mdifferentiableAt (hc.mdifferentiableAt (by simp))]
  rw [mfderiv_eq_fderiv]
  change (fderiv ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p)).comp
    (mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p) = _
  have heq : fderiv ℝ (f ∘ planeCoordinateIsometry) (chart (i : M) p) =
      (fderiv ℝ f (planeCoordinateIsometry (chart (i : M) p))).comp
        planeCoordinateIsometry.toContinuousLinearEquiv.toContinuousLinearMap := by
    exact (hd.hasFDerivAt.comp _ planeCoordinateIsometry.toContinuousLinearEquiv.hasFDerivAt).fderiv
  rw [heq]
  exact ContinuousLinearMap.comp_assoc _ _ _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual metric and linearized metric of supported restored displacements
in the original atlas coordinates. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology Manifold BigOperators
namespace ClosedSurfaceR4
open FiniteOrderSmoothing JetPolynomial

lemma surfaceDifferential_zero_off_support
    {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : M → V) {p : M}
    (hp : p ∉ tsupport F) : surfaceDifferential F p = 0 := by
  have he : F =ᶠ[𝓝 p] (fun _ => (0 : V)) := notMem_tsupport_iff_eventuallyEq.mp hp
  unfold surfaceDifferential
  rw [he.mfderiv_eq, mfderiv_const]
  rfl

namespace FiniteOrderSmoothing.SmoothingAtlas
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable (A : SmoothingAtlas M)

lemma restore_plane_metric_on_source (i : A.centers) (f : SmallModes.Base → Space)
    (hf : tsupport f ⊆ (Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∈ (chart (i : M)).source)
    (hd : DifferentiableAt ℝ f (planeCoordinateIsometry (chart (i : M) p)))
    (v w : TangentSpace planeModel p) :
    inducedForm (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p v w =
      PhaseMean.evaluate
        (RealModes.realMetricTensor (spaceCoordinates ∘ f)
          (planeCoordinateIsometry (chart (i : M) p)))
        (planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v))
        (planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p w)) := by
  rw [euclidean_metric_coordinate_value f hd]
  unfold inducedForm
  have he := A.restore_plane_mfderiv i f hf hp hd
  change surfaceDifferential (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p = _ at he
  rw [he]
  rfl

lemma restore_plane_metric_off_support (i : A.centers) (f : SmallModes.Base → Space)
    (hf : tsupport f ⊆ (Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {p : M} (hp : p ∉ tsupport (A.weight i)) (v w : TangentSpace planeModel p) :
    inducedForm (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) p v w = 0 := by
  have hzero := surfaceDifferential_zero_off_support
    (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry))
    (fun h => hp (A.restore_plane_tsupport i f hf h))
  simp only [inducedForm,hzero,zero_apply,inner_zero_right]

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalOscillatoryModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global phase/amplitude representatives of the actual supported oscillations. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

lemma realMode_zero {n : ℕ} (θ : ℝ) : realMode θ (0 : Fin n → ℂ) = 0 := by
  change realPartCLM n (QuadraticMean.phase θ • (0 : Fin n → ℂ)) = 0
  rw [smul_zero,map_zero]

lemma realMode_contDiff {n : ℕ} (τ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => realMode (p.1/τ) p.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) =>
    realPartCLM n (QuadraticMean.phase (p.1/τ) • p.2))
  apply (realPartCLM n).contDiff.comp
  apply ContDiff.smul (f := fun p : ℝ × (Fin n → ℂ) => QuadraticMean.phase (p.1/τ))
    (g := fun p : ℝ × (Fin n → ℂ) => p.2)
  · have ha : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => ((p.1/τ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.div_const τ)
    exact Complex.contDiff_exp.comp (ha.mul contDiff_const)
  · exact contDiff_snd

lemma surfaceMode_tsupport {X : Type*} [TopologicalSpace X] {n : ℕ}
    (τ : ℝ) (φ : X → ℝ) (Z : X → Fin n → ℂ) :
    tsupport (surfaceMode τ φ Z) ⊆ tsupport Z := by
  apply closure_mono
  intro x hx
  change Z x ≠ 0
  intro hz
  exact hx (by simp only [surfaceMode,hz,realMode_zero])

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfaceMode_smooth {n : ℕ} (τ : ℝ) {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) :
    ContMDiff planeModel 𝓘(ℝ,Fin n → ℝ) ∞ (surfaceMode τ φ Z) :=
  (realMode_contDiff τ).contMDiff.comp (hφ.prodMk_space hZ)

variable [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restore_displacement {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : SmallModes.Base → ℝ) (Z : SmallModes.Base → Fin n → ℂ)
    (hZ : tsupport Z ⊆ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    restore (i : M) (A.outer i) (QuadraticMean.displacement τ φ Z ∘ planeCoordinateIsometry) =
      surfaceMode τ (restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry))
        (restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)) := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hp,Function.comp_apply,surfaceMode,
      QuadraticMean.displacement]
    by_cases hz : Z (planeCoordinateIsometry (chart (i : M) p)) = 0
    · simp only [hz,realMode_zero,smul_zero]
    · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hZ (subset_tsupport Z hz))),
        one_smul,one_smul,one_smul]
  · simp only [restore,indicator_of_notMem hp,surfaceMode,realMode_zero]

lemma vectorChartRead_mode_on_support {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin n → ℂ) {x : JetPolynomial.Base}
    (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.vectorChartRead i (surfaceMode τ φ Z) x =
      realMode (A.vectorChartRead i φ x/τ) (A.vectorChartRead i Z x) := by
  rw [A.vectorChartRead_on_support i _ hx,A.vectorChartRead_on_support i _ hx,
    A.vectorChartRead_on_support i _ hx]
  rfl

lemma vectorChartRead_mode_jets {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) (m : ℕ)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    iteratedFDeriv ℝ m (A.vectorChartRead i (surfaceMode τ φ Z)) x =
      iteratedFDeriv ℝ m (fun y =>
        realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)) x := by
  apply iteratedFDeriv_eq_on_tsupport (A.chartWeight_smooth i).continuous
    isOpen_univ (subset_univ _) (A.vectorChartRead_smooth i (surfaceMode_smooth τ hφ hZ)).contDiffOn
    ((realMode_contDiff τ).comp ((A.vectorChartRead_smooth i hφ).prodMk
      (A.vectorChartRead_smooth i hZ))).contDiffOn
    (fun y hy => A.vectorChartRead_mode_on_support i τ φ Z (A.chartWeight_tsupport i ▸ hy)) m
  rwa [A.chartWeight_tsupport]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasGlobalFreeModes
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite free correction is an actual sum of globally smooth phase modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma coordinateAmplitude_support {K : TopologicalSpace.Compacts JetPolynomial.Base}
    (Z : SupportedField (F := Fin 4 → ℂ) K) :
    tsupport (coordinateAmplitude Z) ⊆ (modeSupport K : Set SmallModes.Base) :=
  (pushSupported planeCoordinateIsometry K Z).tsupport_subset

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ManifoldMetricTensor
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual metric tensors and cross tensors of manifold displacements.
Cross tensors vanish away from the intersection of the two supports. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

local instance metricTensorFiberNormed_r832686_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricTensorFiberSpace_r832686_1 : NormedSpace ℝ TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTangentSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricTensorDualAdd
local instance metricTensorDualSmul_r832686_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance metricTensorSectionNormed_r832686_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricTensorSectionSpace_r832686_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma inducedTensor_apply (F : M → Space) (p : M) (v w : TangentSpace planeModel p) :
    inducedTensor F p v w = inducedForm F p v w := rfl

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RestoredMetricTensor
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restoring a compactly supported Euclidean displacement restores its
actual metric tensor, with no extra terms from the outer atlas cutoff. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMetricFiberSpace
local instance restoredMetricDualSmul_r832686_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMetricFiberNormed
local instance restoredMetricSectionNormed_r832686_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredMetricSectionSpace_r832686_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma restored_metric_tensor (i : A.centers) (f : SmallModes.Base → Space)
    (hf : ContDiff ℝ ∞ f)
    (hsp : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun y =>
        fiberFromThree (RealModes.realMetricTensor (spaceCoordinates ∘ f) (planeCoordinateIsometry y))) := by
  funext p
  ext v w
  by_cases hp : p ∈ (chart (i : M)).source
  · rw [inducedTensor_apply, A.restore_plane_metric_on_source i f hsp hp
      (hf.differentiable (by simp) _), A.tensorRestore_apply i _ hp,
      fiberFromThree_apply]
    have hd := A.plane_chart_differential i hp
    have hv := congrArg (fun L => L v) hd
    have hw := congrArg (fun L => L w) hd
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p v) = _ at hv
    change planeCoordinateIsometry (surfaceDifferential (chart (i : M)) p w) = _ at hw
    simp only [ContinuousLinearMap.comp_apply] at hv hw
    rw [hv,hw]
    by_cases hs : p ∈ tsupport (A.weight i)
    · rw [A.outer_one i p hs,one_mul]
      rfl
    · have hn : planeCoordinateIsometry (chart (i : M) p) ∉ tsupport f := by
        intro hh
        exact hs (A.mem_weight_support_of_plane i hp (hsp hh))
      simp only [euclidean_metric_coordinate_value f (hf.differentiable (by simp) _),
        fderiv_of_notMem_tsupport ℝ hn,zero_apply,inner_zero_right,mul_zero]
  · have hs : p ∉ tsupport (A.weight i) := fun h => hp (A.weight_support i h)
    rw [inducedTensor_apply, A.restore_plane_metric_off_support i f hsp hs]
    have ho : A.outer i p = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hp (A.outer_support i h))
    simp only [bundleRestore,ho,zero_smul,zero_apply]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalModeDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual chart differentials of global oscillatory modes. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma vectorChartRead_mode_fderiv {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    fderiv ℝ (A.vectorChartRead i (surfaceMode τ φ Z)) x =
      fderiv ℝ (fun y => realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)) x := by
  ext v : 1
  have hh := congrArg (fun T => T (fun _ : Fin 1 => v)) (A.vectorChartRead_mode_jets i τ hφ hZ 1 hx)
  simpa only [iteratedFDeriv_one_apply] using hh

lemma vectorPlaneRead_mode_fderiv {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z)
    {x : SmallModes.Base}
    (hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    fderiv ℝ (A.vectorPlaneRead i (surfaceMode τ φ Z)) x =
      fderiv ℝ (QuadraticMean.displacement τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z)) x := by
  obtain ⟨y,hy,rfl⟩ := hx
  let f := fun y => realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)
  have hf : ContDiff ℝ ∞ f := (realMode_contDiff τ).comp
    ((A.vectorChartRead_smooth i hφ).prodMk (A.vectorChartRead_smooth i hZ))
  change fderiv ℝ (A.vectorChartRead i (surfaceMode τ φ Z) ∘ planeCoordinateIsometry.symm) _ =
    fderiv ℝ (f ∘ planeCoordinateIsometry.symm) _
  rw [fderiv_comp _ ((A.vectorChartRead_smooth i (surfaceMode_smooth τ hφ hZ)).differentiable
      (by simp) _) (planeCoordinateIsometry.symm.differentiableAt),
    fderiv_comp _ (hf.differentiable (by simp) _) (planeCoordinateIsometry.symm.differentiableAt),
    LinearIsometryEquiv.symm_apply_apply,A.vectorChartRead_mode_fderiv i τ hφ hZ hy]

omit [CompactSpace M] in
lemma vectorPlaneRead_clm {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (i : A.centers)
    (L : V →L[ℝ] W) (F : M → V) :
    A.vectorPlaneRead i (L ∘ F) = L ∘ A.vectorPlaneRead i F := by
  funext x
  change localize (i : M) (A.outer i) (L ∘ F) (planeCoordinateIsometry.symm x) =
    L (localize (i : M) (A.outer i) F (planeCoordinateIsometry.symm x))
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [localize,hx,map_smul]

omit [CompactSpace M] in
lemma vectorPlaneRead_const_smul {n : ℕ} (i : A.centers) (c : ℂ) (Z : M → Fin n → ℂ) :
    A.vectorPlaneRead i (fun p => c • Z p) = fun x => c • A.vectorPlaneRead i Z x := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target
  · simp only [vectorPlaneRead,vectorChartRead,localize,Function.comp_apply,indicator_of_mem hx]
    exact smul_comm _ _ _
  · simp only [vectorPlaneRead,vectorChartRead,localize,Function.comp_apply,indicator_of_notMem hx,
      smul_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_QuadratureMean
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Recover the zero Fourier mode from two quadrature displacements. -/
noncomputable section
open Set Complex
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.QuadraticMean

lemma conjugate_I_smul {n : ℕ} (B : CVec n) :
    conjugate (Complex.I • B) = (-Complex.I) • conjugate B := by
  ext k
  simp [conjugate,Pi.smul_apply,smul_eq_mul]

lemma zeroPair_quadrature {n : ℕ} (θ : ℝ) (A B : CVec n) :
    2 * zeroPair A B = realMode θ A ⬝ᵥ realMode θ B +
      realMode θ (Complex.I • A) ⬝ᵥ realMode θ (Complex.I • B) := by
  have hc : (Complex.I • A) ⬝ᵥ conjugate (Complex.I • B) = A ⬝ᵥ conjugate B := by
    rw [conjugate_I_smul,smul_dotProduct,dotProduct_smul]
    simp [smul_eq_mul,← mul_assoc]
  have hd : (Complex.I • A) ⬝ᵥ (Complex.I • B) = -(A ⬝ᵥ B) := by
    rw [smul_dotProduct,dotProduct_smul]
    simp [smul_eq_mul,← mul_assoc]
  rw [realMode_self_phase,realMode_self_phase,hc,hd]
  simp only [zeroPair,mul_neg,neg_re]
  ring

lemma derivativeAmplitude_const_smul {n : ℕ} {φ : Base → ℝ} {Z : Base → CVec n}
    {p : Base} (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) (c : ℂ) (v : Base) :
    derivativeAmplitude τ φ (fun x => c • Z x) v p = c • derivativeAmplitude τ φ Z v p := by
  unfold derivativeAmplitude
  have hd : fderiv ℝ (fun x => c • Z x) p = c • fderiv ℝ Z p :=
    (hZ.hasFDerivAt.const_smul c).fderiv
  rw [hd]
  simp only [smul_apply,smul_add,smul_smul]
  congr 1
  rw [mul_comm]

end ClosedSurfaceR4.QuadraticMean
namespace ClosedSurfaceR4.RealModes
open QuadraticMean PhaseMean

lemma phaseZeroTensor_quadrature {n : ℕ} {φ : SmallModes.Base → ℝ}
    {Z : SmallModes.Base → QuadraticMean.CVec n} {p : SmallModes.Base}
    (hφ : DifferentiableAt ℝ φ p) (hZ : DifferentiableAt ℝ Z p) (τ : ℝ) :
    (2 : ℝ) • phaseZeroTensor τ φ Z p =
      realMetricTensor (displacement τ φ Z) p +
      realMetricTensor (displacement τ φ (fun x => Complex.I • Z x)) p := by
  ext k
  simp only [Pi.smul_apply,smul_eq_mul,Pi.add_apply,phaseZeroTensor,realMetricTensor_apply,
    realMetric,SmallModes.coordDeriv]
  have hi : DifferentiableAt ℝ (fun x => Complex.I • Z x) p := hZ.const_smul Complex.I
  rw [derivative_displacement hφ hZ,derivative_displacement hφ hZ,
    derivative_displacement hφ hi,
    derivative_displacement hφ hi,
    derivativeAmplitude_const_smul hZ,derivativeAmplitude_const_smul hZ]
  exact zeroPair_quadrature _ _ _

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_GlobalQuadraticModes
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global quadratic phase expansion, retaining all cross-chart interactions. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.globalModeMetricDualAdd
local instance globalModeMetricFiberNormed_r832686_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance globalModeMetricFiberSpace_r832686_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance globalModeMetricDualSmul_r832686_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance globalModeMetricSectionNormed_r832686_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance globalModeMetricSectionSpace_r832686_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem global_mode_metric (τ : ℝ) (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ Z) :
    inducedTensor (spaceCoordinates.symm ∘ surfaceMode τ φ Z) =
      A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
        RealModes.realMetricTensor (QuadraticMean.displacement τ
          (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z)) x) := by
  have he (i : A.centers) :
      spaceCoordinates ∘ A.vectorPlaneRead i (spaceCoordinates.symm ∘ surfaceMode τ φ Z) =
        A.vectorPlaneRead i (surfaceMode τ φ Z) := by
    have hr : A.vectorPlaneRead i (spaceCoordinates.symm ∘ surfaceMode τ φ Z) =
        spaceCoordinates.symm ∘ A.vectorPlaneRead i (surfaceMode τ φ Z) :=
      A.vectorPlaneRead_clm i spaceCoordinates.symm.toContinuousLinearMap (surfaceMode τ φ Z)
    rw [hr]
    funext x
    exact spaceCoordinates.apply_symm_apply _
  rw [← A.metric_from_chart_reads
    (spaceCoordinates.symm.contDiff.contMDiff.comp (surfaceMode_smooth τ hφ hZ))]
  simp_rw [he]
  congr 1
  funext i x
  by_cases hw : A.planeWeight i x = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul]
  · have hx : x ∈ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
      (A.supportedPlaneWeight i).tsupport_subset (subset_tsupport (A.planeWeight i) hw)
    have hd := A.vectorPlaneRead_mode_fderiv i τ hφ hZ hx
    congr 1
    ext k
    simp only [RealModes.realMetricTensor_apply,RealModes.realMetric,SmallModes.coordDeriv,hd]

theorem global_zeroPhase_quadrature (τ : ℝ) (φ : M → ℝ) (Z : M → Fin 4 → ℂ)
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ Z) :
    (2 : ℝ) • A.tensorPlaneRestore (fun i x => (A.planeWeight i x)^2 •
      RealModes.phaseZeroTensor τ (A.vectorPlaneRead i φ) (A.vectorPlaneRead i Z) x) =
      inducedTensor (spaceCoordinates.symm ∘ surfaceMode τ φ Z) +
      inducedTensor (spaceCoordinates.symm ∘ surfaceMode τ φ (fun p => Complex.I • Z p)) := by
  have hIc : ContDiff ℝ ∞ (fun z : Fin 4 → ℂ => Complex.I • z) :=
    (contDiff_const (c := Complex.I)).smul contDiff_id
  have hi : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (fun p => Complex.I • Z p) :=
    hIc.contMDiff.comp hZ
  rw [A.global_mode_metric τ φ Z hφ hZ,A.global_mode_metric τ φ _ hφ hi,
    ← A.tensorPlaneRestore_add,← A.tensorPlaneRestore_smul]
  congr 1
  funext i x
  simp only [Pi.smul_apply,Pi.add_apply,A.vectorPlaneRead_const_smul]
  rw [smul_comm (2 : ℝ) ((A.planeWeight i x)^2),
    RealModes.phaseZeroTensor_quadrature
      ((A.vectorPlaneRead_smooth i hφ).differentiable (by simp) x)
      ((A.vectorPlaneRead_smooth i hZ).differentiable (by simp) x),smul_add]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RealRestoredMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real-coordinate version of the supported metric restoration identity. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.realRestoredMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.realRestoredMetricFiberSpace
local instance realRestoredMetricDualSmul_r832686_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.realRestoredMetricFiberNormed
local instance realRestoredMetricSectionNormed_r832686_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance realRestoredMetricSectionSpace_r832686_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma real_restored_metric (i : A.centers) (f : SmallModes.Base → RealModes.RVec 4)
    (hf : ContDiff ℝ ∞ f)
    (hsp : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    inducedTensor (spaceCoordinates.symm ∘ restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry)) =
      A.bundleRestore A.tensorTriv i (fun y =>
        fiberFromThree (RealModes.realMetricTensor f (planeCoordinateIsometry y))) := by
  have hrest := A.restored_metric_tensor i (spaceCoordinates.symm ∘ f)
    (spaceCoordinates.symm.contDiff.comp hf)
    ((tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) f).trans hsp)
  have he : restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ f) ∘ planeCoordinateIsometry) =
      spaceCoordinates.symm ∘ restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source <;>
      simp [restore,hp,Function.comp_apply,map_smul]
  have hcoord : spaceCoordinates ∘ (spaceCoordinates.symm ∘ f) = f := by
    funext x
    exact spaceCoordinates.apply_symm_apply _
  rw [he,hcoord] at hrest
  exact hrest

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_RestoredQuadratureMean
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the actual zero Fourier coefficient through supported atlas restoration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMeanDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMeanFiberSpace
local instance restoredMeanDualSmul_r832686_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredMeanFiberNormed
local instance restoredMeanSectionNormed_r832686_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredMeanSectionSpace_r832686_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem restored_zeroPhase (i : A.centers) (τ : ℝ)
    (φ : SmallModes.Base → ℝ) (Z : SmallModes.Base → Fin 4 → ℂ)
    (hφ : ContDiff ℝ ∞ φ) (hZ : ContDiff ℝ ∞ Z)
    (hs : tsupport Z ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    let Φ := restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry)
    let W := restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)
    A.tensorPlaneRestore (fun j x => (A.planeWeight j x)^2 •
      RealModes.phaseZeroTensor τ (A.vectorPlaneRead j Φ) (A.vectorPlaneRead j W) x) =
    A.bundleRestore A.tensorTriv i (fun y =>
      fiberFromThree (RealModes.phaseZeroTensor τ φ Z (planeCoordinateIsometry y))) := by
  dsimp only
  let Φ := restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry)
  let W := restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)
  let ZI := fun x => Complex.I • Z x
  have hΦ : ContMDiff planeModel 𝓘(ℝ) ∞ Φ := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) (hφ.comp planeCoordinateIsometry.contDiff)
  have hW : ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ W := restore_smooth (i : M)
    (A.outer_smooth i) (A.outer_support i) (hZ.comp planeCoordinateIsometry.contDiff)
  have hZI : ContDiff ℝ ∞ ZI := (contDiff_const (c := Complex.I)).smul hZ
  have hsI : tsupport ZI ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (tsupport_smul_subset_right (fun _ => Complex.I) Z).trans hs
  have hWI : (fun p => Complex.I • W p) =
      restore (i : M) (A.outer i) (ZI ∘ planeCoordinateIsometry) := by
    funext p
    by_cases hp : p ∈ (chart (i : M)).source
    · simp only [W,ZI,restore,indicator_of_mem hp,Function.comp_apply]
      exact smul_comm _ _ _
    · simp only [W,restore,indicator_of_notMem hp,smul_zero]
  have hdisp := contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn hZ.contDiffOn τ)
  have hdispI := contDiffOn_univ.mp (RealModes.contDiffOn_displacement hφ.contDiffOn hZI.contDiffOn τ)
  have hsdisp : tsupport (QuadraticMean.displacement τ φ Z) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (surfaceMode_tsupport τ φ Z).trans hs
  have hsdispI : tsupport (QuadraticMean.displacement τ φ ZI) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) :=
    (surfaceMode_tsupport τ φ ZI).trans hsI
  have he := A.global_zeroPhase_quadrature τ Φ W hΦ hW
  rw [hWI,← A.restore_displacement i τ φ Z hs,← A.restore_displacement i τ φ ZI hsI,
    A.real_restored_metric i _ hdisp hsdisp,A.real_restored_metric i _ hdispI hsdispI] at he
  have hc :
      (fun y => fiberFromThree (RealModes.realMetricTensor (QuadraticMean.displacement τ φ Z)
        (planeCoordinateIsometry y))) +
      (fun y => fiberFromThree (RealModes.realMetricTensor (QuadraticMean.displacement τ φ ZI)
        (planeCoordinateIsometry y))) =
      (2 : ℝ) • (fun y => fiberFromThree (RealModes.phaseZeroTensor τ φ Z (planeCoordinateIsometry y))) := by
    funext y
    change fiberFromThree _ + fiberFromThree _ = (2 : ℝ) • fiberFromThree _
    rw [← map_add,← RealModes.phaseZeroTensor_quadrature
      (hφ.differentiable (by simp) _) (hZ.differentiable (by simp) _) τ,map_smul]
  rw [← A.bundleRestore_add,hc,A.bundleRestore_smul] at he
  funext p
  ext v w
  have hv := congrArg (fun T => T p v w) he
  change (2 : ℝ) * _ = 2 * _ at hv
  exact mul_left_cancel₀ (by norm_num : (2 : ℝ) ≠ 0) hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorRestoreFinite
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite-sum linearity of the actual tensor restoration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorRestoreFiniteDualAdd
local instance tensorRestoreFiniteFiberNormed_r832686_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance tensorRestoreFiniteFiberSpace_r832686_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance tensorRestoreFiniteDualSmul_r832686_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance tensorRestoreFiniteSectionNormed_r832686_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance tensorRestoreFiniteSectionSpace_r832686_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorPlaneRestore_sum {ι : Type*} [Fintype ι]
    (f : ι → A.centers → SmallModes.Base → PhaseMean.Tensor) :
    A.tensorPlaneRestore (∑ j, f j) = ∑ j, A.tensorPlaneRestore (f j) :=
  map_sum A.tensorPlaneRestoreLM f Finset.univ

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_FiniteAtlasFreeMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact global free-mode identities for an arbitrary finite family in
each fixed atlas chart. This accommodates the variable number of grid cells. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberSpace
local instance finiteAtlasFreeDualSmul_r832686_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)
variable {ι : A.centers → Type*} [∀ i, Fintype (ι i)]
    {n : A.centers → ℕ} {P : ∀ i, Fin 3 → Fin (n i) → Expression}
    {G : A.centers → Base → JetPolynomial.Space} {hG : ∀ i, ContDiff ℝ ∞ (G i)}
    {φ : ∀ i, ι i → Base → ℝ} {K : ∀ i, ι i → TopologicalSpace.Compacts Base}
    {τ : ℝ} {s : ℝ≥0}
    {c : ∀ i j, PolynomialSolveData (P i) 0 (G i) (hG i) (φ i j) (K i j) τ s}
    {r : A.centers → ℝ} {ρ R : ℝ}
    {reference : A.centers → SmallModes.Base → Tensor}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.finiteAtlasFreeFiberNormed
local instance finiteAtlasFreeSectionNormed_r832686_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance finiteAtlasFreeSectionSpace_r832686_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finiteAtlasIndexDecidable
theorem finite_atlas_zeroPhase_oai
    (d : ∀ i j, ChartedMeanData (c i j) (r i) ρ R (reference i))
    (hρ : 0 < ρ) (δ : ℝ) (q : ℕ) (u : ∀ x : M, CovariantTwoTensor x)
    (hK : ∀ i j, (modeSupport (K i j) : Set SmallModes.Base) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.tensorPlaneRestore (fun k x => (A.planeWeight k x)^2 • RealModes.zeroPhaseSum τ
      (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
      (fun a : Σ i, ι i => A.vectorPlaneRead k
        (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x) =
    A.tensorPlaneRestore (fun i => RealModes.zeroPhaseSum τ
      (fun j => coordinatePhase (φ i j))
      (fun j => coordinateAmplitude ((d i j).freeAmplitude hρ δ q (A.tensorPlaneRead i u)))) := by
  classical
  let Z₀ := fun (a : Σ i, ι i) => RealModes.phaseZeroTensor τ
    (coordinatePhase (φ a.1 a.2))
    (coordinateAmplitude ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
  let T := fun (a : Σ i, ι i) (k : A.centers) (x : SmallModes.Base) =>
    (A.planeWeight k x)^2 • RealModes.phaseZeroTensor τ
      (A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
      (A.vectorPlaneRead k (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x
  have ht (a : Σ i, ι i) : A.tensorPlaneRestore (T a) =
      A.bundleRestore A.tensorTriv a.1 (fun y => fiberFromThree (Z₀ a (planeCoordinateIsometry y))) := by
    have hs := (coordinateAmplitude_support
      ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u))).trans (hK a.1 a.2)
    have hh := A.restored_zeroPhase a.1 τ (coordinatePhase (φ a.1 a.2))
      (coordinateAmplitude ((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)))
      ((c a.1 a.2).smoothPhase.comp planeCoordinateIsometry.symm.contDiff)
      (((d a.1 a.2).freeAmplitude hρ δ q (A.tensorPlaneRead a.1 u)).contDiff.comp
        planeCoordinateIsometry.symm.contDiff) hs
    simpa only [T,Z₀,finiteGlobalPhase,finiteGlobalAmplitude,coordinatePhase,coordinateAmplitude,
      Function.comp_def,LinearIsometryEquiv.symm_apply_apply] using hh
  have he : (fun k x => (A.planeWeight k x)^2 • RealModes.zeroPhaseSum τ
      (fun a : Σ i, ι i => A.vectorPlaneRead k (A.finiteGlobalPhase (φ := φ) a.1 a.2))
      (fun a : Σ i, ι i => A.vectorPlaneRead k
        (A.finiteGlobalAmplitude d hρ δ q u a.1 a.2)) x) = ∑ a : Σ i, ι i, T a := by
    funext k x
    simp only [T,RealModes.zeroPhaseSum,Finset.smul_sum,Finset.sum_apply]
  rw [he,A.tensorPlaneRestore_sum]
  simp_rw [ht]
  rw [Fintype.sum_sigma]
  funext p
  simp only [tensorPlaneRestore,RealModes.zeroPhaseSum,Z₀,Finset.sum_apply,
    bundleRestore,map_sum,Finset.smul_sum]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase_oai.{u_1, u_2} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.finite_atlas_zeroPhase_oai.{u_1, u_2}
