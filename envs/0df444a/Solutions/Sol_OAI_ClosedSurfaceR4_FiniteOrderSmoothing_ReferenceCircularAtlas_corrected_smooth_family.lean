-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:32:13.396693+00:00
-- url     : https://prove2.me/submissions/346f738a-8983-4e36-83ba-82ed29942be6

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
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_circular_operator_metric_stability
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_correctedPrimitiveAmplitude_smooth_of_data

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

lemma convexQuadraticPhase_smooth (ell : Base) (L : ℝ) :
    ContDiff ℝ ∞ (convexQuadraticPhase ell L) := by
  exact (phaseLinear ell).contDiff.add
    (contDiff_const.mul ((contDiff_fst.pow 2).add (contDiff_snd.pow 2)))

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
attribute [-instance] _root_.instVAddIntReal_solutions
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

lemma perturbedPhaseOperator_smooth (P : PhaseBasis) :
    ContDiff ℝ ∞ (perturbedPhaseOperator P) := by
  apply ContDiff.sum
  intro i _
  apply contDiff_const.smulRight
  apply contDiff_pi.mpr
  intro j
  fin_cases j <;> simp only [covectorSquare, Matrix.cons_val_zero',
    Matrix.cons_val_succ'] <;> fun_prop

lemma perturbedPhaseCoefficient_smoothAt (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : (perturbedPhaseOperator P xi).IsInvertible) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun z => perturbedPhaseCoefficient P z i) xi :=
  contDiffAt_const.clm_comp
    (hxi.contDiffAt_map_inverse.comp xi (perturbedPhaseOperator_smooth P).contDiffAt)

end ClosedSurfaceR4.PhaseGeometry

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SpatialPhaseBasis
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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

lemma admissiblePhaseCovectors_eventually {P : PhaseBasis} {xi : Fin 3 → Base}
    (hxi : admissiblePhaseCovectors P xi) :
    ∀ᶠ z in 𝓝 xi, admissiblePhaseCovectors P z := by
  have hA : ∀ᶠ z in 𝓝 xi, (perturbedPhaseOperator P z).IsInvertible :=
    (perturbedPhaseOperator_smooth P).continuous.continuousAt.eventually hxi.1.eventually_nhds
  have hn : ∀ᶠ z in 𝓝 xi, ∀ i, z i ≠ 0 := by
    rw [Filter.eventually_all]
    intro i
    exact (continuous_apply i).continuousAt.eventually_ne (hxi.2 i)
  exact hA.and hn

lemma resolvedPhaseBasis_coefficients (P : PhaseBasis) {xi : Fin 3 → Base}
    (hxi : admissiblePhaseCovectors P xi) (i : Fin 3) :
    (resolvedPhaseBasis P xi).Q i = perturbedPhaseCoefficient P xi i := by
  simp only [resolvedPhaseBasis,dite_eq_left hxi]

lemma resolvedPhaseBasis_coefficient_smoothAt (P : PhaseBasis)
    {xi : Base → Fin 3 → Base} {p : Base} (hxi : ContDiffAt ℝ ∞ xi p)
    (hp : admissiblePhaseCovectors P (xi p)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (resolvedPhaseBasis P (xi x)).Q i) p := by
  have he : (fun x => (resolvedPhaseBasis P (xi x)).Q i) =ᶠ[𝓝 p]
      (fun x => perturbedPhaseCoefficient P (xi x) i) := by
    have hnear : ∀ᶠ x in 𝓝 p, admissiblePhaseCovectors P (xi x) :=
      hxi.continuousAt.eventually (admissiblePhaseCovectors_eventually hp)
    filter_upwards [hnear] with x hx
    exact resolvedPhaseBasis_coefficients P hx i
  exact ((perturbedPhaseCoefficient_smoothAt P hp.1 i).comp p hxi).congr_of_eventuallyEq he

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

lemma centeredConvexPhase_smooth (ell : Base) (L : ℝ) (c : Base) :
    ContDiff ℝ ∞ (centeredConvexPhase ell L c) :=
  (convexQuadraticPhase_smooth ell L).comp (contDiff_id.sub contDiff_const)

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

lemma centeredSpatialBasis_coefficient_smoothAt (P : PhaseBasis) (ell : Fin 3 → Base)
    (L : ℝ) (c : Base) {p : Base}
    (hp : admissiblePhaseCovectors P
      (fun i => phaseDerivative (centeredConvexPhase (ell i) L c) p)) (i : Fin 3) :
    ContDiffAt ℝ ∞ (fun x => (centeredSpatialBasis P ell L c x).Q i) p := by
  have hs : ContDiffAt ℝ ∞
      (fun x : Base => fun j : Fin 3 => phaseDerivative (centeredConvexPhase (ell j) L c) x) p := by
    apply contDiffAt_pi.mpr
    intro j
    simp only [centeredConvexPhase_phaseDerivative]
    exact contDiffAt_const.add ((contDiffAt_id.sub contDiffAt_const).const_smul L)
  exact resolvedPhaseBasis_coefficient_smoothAt P hs hp i

end ClosedSurfaceR4.PhaseGeometry

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
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instVAddIntReal_solutions
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

variable [IsManifold planeModel ∞ M]

variable [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_compact (p : M) (r : ℝ)
    (hregion : circularCoordinateRegion p r ⊆ (coordinateChart p).target) :
    IsCompact (circularDiskClosure p r) :=
  (circularCoordinateRegion_compact p r).image_of_continuousOn
    ((coordinateChart p).continuousOn_symm.mono hregion)

end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CurvedAtlasPrimitives
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positive primitive amplitudes for point-dependent phase bases.
The basis can be the actual nonlinear gradient basis constructed in
`SpatialPhaseBasis`; no constant-phase restriction enters the algebra. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
local instance curvedPrimitiveFiberNormed_raff5a3_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance curvedPrimitiveFiberSpace_raff5a3_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance curvedPrimitiveDualAdd_raff5a3_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance curvedPrimitiveDualSmul_raff5a3_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M) (P : A.centers → JetPolynomial.Base → PhaseBasis)
  (u : ∀ p : M, CovariantTwoTensor p)

local instance curvedPrimitiveSectionNormed_raff5a3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance curvedPrimitiveSectionSpace_raff5a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma curvedAtlasPhase_smooth (phi : A.centers → Fin 3 → SmallModes.Base → ℝ)
    (hphi : ∀ i j, ContDiff ℝ ∞ (phi i j)) (a : A.centers × Fin 3) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (A.curvedAtlasPhase phi a) :=
  restore_smooth (a.1 : M) (A.outer_smooth a.1) (A.outer_support a.1)
    ((hphi a.1 a.2).comp JetPolynomial.planeCoordinateIsometry.contDiff)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveFiberInverse
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite rank-one correction acts on symmetric tensors. Adding the
identity on the antisymmetric summand gives an honest invertible operator
on the full four-dimensional tensor fiber, without an orientation choice. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseFiberNormed
local instance primitiveInverseFiberSpace_raff5a3_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance primitiveInverseFiberComplete_raff5a3_1 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitiveInverseFiberGroup
lemma tensorSymmetrizer_apply (B : TensorFiber) (v w : Plane) :
    tensorSymmetrizer B v w = (B v w+B w v)/2 := by
  change (1/2 : ℝ)*(B v w+B w v) = (B v w+B w v)/2
  ring

lemma tensorSymmetrizer_symmetric (B : TensorFiber) (v w : Plane) :
    tensorSymmetrizer B v w = tensorSymmetrizer B w v := by
  rw [tensorSymmetrizer_apply,tensorSymmetrizer_apply,add_comm]

lemma tensorSymmetrizer_eq_self {B : TensorFiber} (hB : ∀ v w, B v w = B w v) :
    tensorSymmetrizer B = B := by
  ext v w
  rw [tensorSymmetrizer_apply,hB v w]
  ring

variable {ι : Type*} [Fintype ι]

lemma finitePrimitiveOperator_apply (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    finitePrimitiveOperator q psi xi B =
      ∑ i, ((psi i)^2*q i (tensorSymmetrizer B)) • ((xi i).smulRight (xi i)) := by
  simp only [finitePrimitiveOperator,sum_apply,smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.comp_apply,smul_smul]

lemma finitePrimitiveOperator_symmetric (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) (v w : Plane) :
    finitePrimitiveOperator q psi xi B v w = finitePrimitiveOperator q psi xi B w v := by
  simp only [finitePrimitiveOperator_apply,sum_apply,smul_apply,smul_eq_mul,
    ContinuousLinearMap.smulRight_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma completedPrimitiveOperator_apply (q : ι → TensorFiber →L[ℝ] ℝ)
    (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ) (B : TensorFiber) :
    completedPrimitiveOperator q psi xi B =
      finitePrimitiveOperator q psi xi B+B-tensorSymmetrizer B := rfl

/-- The inverse of the completed operator solves precisely the original
symmetric rank-one equation; the auxiliary antisymmetric identity vanishes. -/
theorem completedPrimitiveOperator_inverse_symmetric
    (q : ι → TensorFiber →L[ℝ] ℝ) (psi : ι → ℝ) (xi : ι → Plane →L[ℝ] ℝ)
    (hinv : (completedPrimitiveOperator q psi xi).IsInvertible)
    {H : TensorFiber} (hH : ∀ v w, H v w = H w v) :
    let B := (completedPrimitiveOperator q psi xi).inverse H
    (∀ v w, B v w = B w v) ∧ finitePrimitiveOperator q psi xi B = H := by
  dsimp only
  let B := (completedPrimitiveOperator q psi xi).inverse H
  have hsolve : completedPrimitiveOperator q psi xi B = H := hinv.self_apply_inverse H
  have hsym : ∀ v w, B v w = B w v := by
    intro v w
    have hvw := congrArg (fun C : TensorFiber => C v w) hsolve
    have hwv := congrArg (fun C : TensorFiber => C w v) hsolve
    have hfin := finitePrimitiveOperator_symmetric q psi xi B v w
    rw [completedPrimitiveOperator_apply] at hvw hwv
    simp only [add_apply,sub_apply] at hvw hwv
    have hs := tensorSymmetrizer_symmetric B v w
    have ht := hH v w
    linarith
  refine ⟨hsym,?_⟩
  rw [completedPrimitiveOperator_apply,tensorSymmetrizer_eq_self hsym,add_sub_cancel_right] at hsolve
  exact hsolve

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPrimitiveOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fiberwise correction operator for independently perturbed
primitive cutoffs. Its reference value is the identity, and its inverse
solves the finite rank-one equation on the original tensor bundle. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseMean PhaseGeometry

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberSpace
local instance atlasOperatorFiberComplete_raff5a3_1 : CompleteSpace TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorFiberSpace
local instance atlasOperatorFiberComplete_raff5a3_2 : CompleteSpace TensorFiber := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionNormed
local instance atlasOperatorSectionSpace_raff5a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.atlasOperatorSectionGroup
theorem correctedPrimitiveTensor_reconstruct
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p) (hsymm : ∀ p v w, u p v w = u p w v) (p : M) :
    (∀ v w, A.correctedPrimitiveTensor P psi phi u p v w =
      A.correctedPrimitiveTensor P psi phi u p w v) ∧
    (∑ a : A.centers × Fin 3, ((psi a p)^2 * A.primitiveCoefficientField P a p
      (A.correctedPrimitiveTensor P psi phi u p)) •
      (A.primitivePhaseCovector phi a p).smulRight (A.primitivePhaseCovector phi a p)) = u p := by
  obtain ⟨hs,he⟩ := completedPrimitiveOperator_inverse_symmetric
    (fun a => A.primitiveCoefficientField P a p) (fun a => psi a p)
    (fun a => A.primitivePhaseCovector phi a p) (hinv p) (hsymm p)
  refine ⟨hs,?_⟩
  rw [finitePrimitiveOperator_apply] at he
  simpa only [correctedPrimitiveTensor,primitiveFullOperator,tensorSymmetrizer_eq_self hs] using! he

lemma correctedPrimitiveAmplitude_square
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 ≤ A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) (p : M) :
    (A.correctedPrimitiveAmplitude P psi phi u a p)^2 =
      (psi a p)^2*A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p) := by
  by_cases hp : psi a p = 0
  · simp only [correctedPrimitiveAmplitude,hp,zero_mul,zero_pow (by decide : 2 ≠ 0)]
  · rw [correctedPrimitiveAmplitude,mul_pow,Real.sq_sqrt (hpos a p (subset_tsupport _ hp))]

/-- Independent supports retain the exact global rank-one tensor identity. -/
theorem correctedPrimitiveAmplitude_reconstruct
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (hinv : ∀ p, (A.primitiveFullOperator P psi phi p).IsInvertible)
    (u : ∀ p : M, CovariantTwoTensor p) (hsymm : ∀ p v w, u p v w = u p w v)
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 ≤ A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (p : M) :
    (∑ a : A.centers × Fin 3, (A.correctedPrimitiveAmplitude P psi phi u a p)^2 •
      (A.primitivePhaseCovector phi a p).smulRight (A.primitivePhaseCovector phi a p)) = u p := by
  simp_rw [A.correctedPrimitiveAmplitude_square P psi phi u hpos]
  exact (A.correctedPrimitiveTensor_reconstruct P psi phi hinv u hsymm p).2

lemma correctedPrimitiveAmplitude_pos_iff
    (P : A.centers → JetPolynomial.Base → PhaseBasis)
    (psi : (A.centers × Fin 3) → M → ℝ) (phi : (A.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hpos : ∀ a p, p ∈ tsupport (psi a) →
      0 < A.primitiveCoefficientField P a p (A.correctedPrimitiveTensor P psi phi u p))
    (a : A.centers × Fin 3) (p : M) :
    0 < A.correctedPrimitiveAmplitude P psi phi u a p ↔ 0 < psi a p := by
  constructor
  · intro h
    exact (mul_pos_iff.mp h).resolve_right
      (fun hh => (Real.sqrt_nonneg _).not_gt hh.2) |>.1
  · intro h
    exact mul_pos h (Real.sqrt_pos.mpr (hpos a p (subset_tsupport _ h.ne')))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularDiskTopology
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual coordinate disks are regular open, with exactly the stated
coordinate circles as their frontiers. -/
noncomputable section
open Set Filter Metric Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [T2Space M]

omit [IsManifold planeModel ∞ M] [T2Space M] in
lemma circularDiskClosure_iff (q : M) {r : ℝ}
    (hreg : circularCoordinateRegion q r ⊆ (coordinateChart q).target) (p : M) :
    p ∈ circularDiskClosure q r ↔ p ∈ (coordinateChart q).source ∧
      circularRadiusSquared (coordinateChart q q) (coordinateChart q p) ≤ r^2 := by
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨(coordinateChart q).map_target (hreg hx),?_⟩
    rwa [(coordinateChart q).right_inv (hreg hx)]
  · rintro ⟨hp,hx⟩
    exact ⟨coordinateChart q p,hx,(coordinateChart q).left_inv hp⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentCircularRealization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite geometric iteration using independently chosen local
convex phases and one fixed background norm for all prefix bounds. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]

omit [CompactSpace M] in
lemma circular_weight_support {B : SmoothingAtlas M} (r : B.centers → ℝ)
    (hreg : ∀ i : B.centers, circularCoordinateRegion (i : M) (r i) ⊆ (coordinateChart (i : M)).target)
    (hnon : ∀ i p, 0 ≤ B.weight i p)
    (hpos : ∀ i p, 0 < B.weight i p ↔ p ∈ circularCoordinateDisk (i : M) (r i))
    (i : B.centers) : tsupport (B.weight i) ⊆ circularDiskClosure (i : M) (r i) := by
  apply closure_minimal _ (circularDiskClosure_compact (i : M) (r i) (hreg i)).isClosed
  intro p hp
  have hd := (hpos i p).mp (lt_of_le_of_ne (hnon i p) (Ne.symm hp))
  exact (circularDiskClosure_iff (i : M) (hreg i) p).mpr ⟨hd.1,hd.2.le⟩

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ReferenceCircularOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected reference atlas supplies the actual identity operator,
smooth coefficient germs, and positive metric coefficients. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes PhaseMean PhaseGeometry
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

omit [CompactSpace M] in
lemma supported (i : d.B.centers) :
    tsupport (d.B.weight i) ⊆ circularDiskClosure (i : M) (d.radius i) :=
  circular_weight_support d.radius d.region d.weight_nonneg d.weight_positive i

omit [CompactSpace M] in
lemma basis_smooth (i : d.B.centers) {p : M} (hp : p ∈ tsupport (d.B.weight i)) (j : Fin 3) :
    ContDiffAt ℝ ∞ (fun y => (d.basis i y).Q j) (chart (i : M) p) := by
  exact (centeredSpatialBasis_coefficient_smoothAt _ _ _ _
    (d.admissible i p (d.supported i hp)) j).comp (chart (i : M) p)
      JetPolynomial.planeCoordinateIsometry.contDiff.contDiffAt

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ReferenceCorrectedFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual positive smooth primitive decompositions of every nearby
remainder, using independently perturbed supported weights and phases. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.referenceFamilyFiberSpace
local instance referenceFamilyDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance referenceFamilyDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.referenceFamilyFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.referenceFamilyFiberSpace
local instance referenceFamilySectionNormed_raff5a3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance referenceFamilySectionSpace_raff5a3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem corrected_smooth_family_oai {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ phaseTol weightTol mapTol : ℝ, 0 < phaseTol ∧ 0 < weightTol ∧ 0 < mapTol ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < phaseTol) →
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
      (∀ a p, 0 ≤ psi a p) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < weightTol) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mapTol (G-F) →
      ∃ f : SmoothPrimitiveFamily (d.B.centers × Fin 3) (g.inner-inducedTensor (r • G)),
        f.phase = d.perturbedPhases ell ∧
        f.amplitude = d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
          (g.inner-inducedTensor (r • G)) ∧
        (∀ a p, 0 ≤ f.amplitude a p) ∧
        (∀ a p, 0 < f.amplitude a p ↔ 0 < psi a p) ∧
        ∀ a, tsupport (f.amplitude a) ⊆ tsupport (psi a) := by
  obtain ⟨pt,wt,mt,hpt,hwt,hmt,hstable⟩ := d.circular_operator_metric_stability hF r href
  refine ⟨pt,wt,mt,hpt,hwt,hmt,?_⟩
  intro ell psi hell hpsi hnon hs hw G hG hnear
  obtain ⟨hinv,hpos⟩ := hstable ell psi hell hs hw G hG hnear
  let phi := d.perturbedPhases ell
  let u := g.inner-inducedTensor (r • G)
  have hphi (a : d.B.centers × Fin 3) : ContMDiff planeModel 𝓘(ℝ) ∞ (phi a) :=
    d.B.curvedAtlasPhase_smooth (d.B.centeredPhaseFamily ell d.L)
      (fun _ _ => PhaseGeometry.centeredConvexPhase_smooth _ _ _) a
  have hscaled : ContMDiff planeModel spaceModel ∞ (r • G) :=
    (show ContMDiff planeModel 𝓘(ℝ) ∞ (fun _ : M => r) from contMDiff_const).smul hG
  have hu : ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (u p)) :=
    g.contMDiff.sub_section (A.inducedTensor_smooth hscaled)
  have hsym : ∀ p v w, u p v w = u p w v := by
    intro p v w
    change g.inner p v w-inner ℝ (mfderiv planeModel spaceModel (r • G) p v)
      (mfderiv planeModel spaceModel (r • G) p w) =
      g.inner p w v-inner ℝ (mfderiv planeModel spaceModel (r • G) p w)
      (mfderiv planeModel spaceModel (r • G) p v)
    rw [g.symm,real_inner_comm]
  have hp : ∀ a p, p ∈ tsupport (psi a) →
      0 < d.B.primitiveCoefficientField d.basis a p
        (d.B.correctedPrimitiveTensor d.basis psi phi u p) :=
    fun a p hp => hpos a p (hs a hp)
  let amp := d.B.correctedPrimitiveAmplitude d.basis psi phi u
  let f : SmoothPrimitiveFamily (d.B.centers × Fin 3) u := {
    amplitude := amp
    phase := phi
    smoothAmplitude := fun a => d.B.correctedPrimitiveAmplitude_smooth_of_data
      d.basis psi phi hpsi hphi (fun a => (hs a).trans (d.B.weight_support a.1))
      (fun a p ha => d.basis_smooth a.1 (hs a ha) a.2) d.outer hinv u hu hp a
    smoothPhase := hphi
    sum_eq := d.B.correctedPrimitiveAmplitude_reconstruct d.basis psi phi hinv u hsym
      (fun a p ha => (hp a p ha).le) }
  refine ⟨f,rfl,rfl,?_,?_,?_⟩
  · intro a p
    exact mul_nonneg (hnon a p) (Real.sqrt_nonneg _)
  · exact d.B.correctedPrimitiveAmplitude_pos_iff d.basis psi phi u hp
  · intro a
    exact tsupport_mul_subset_left

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.corrected_smooth_family_oai.{u_1}
