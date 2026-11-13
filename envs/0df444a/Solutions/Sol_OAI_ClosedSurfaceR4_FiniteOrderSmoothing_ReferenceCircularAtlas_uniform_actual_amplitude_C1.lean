-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:44.969869+00:00
-- url     : https://prove2.me/submissions/be9c1294-5262-4e17-95df-f7f8ff5f8ffc

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_ReferenceCircularAtlas_actual_amplitude_parameter_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_correctedAmplitude_coordinate_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_primitiveCoordinateData_fderiv_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_tensorFrameRead_C1_bound

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

namespace SmoothingAtlas

variable (A : SmoothingAtlas M)

variable [CompactSpace M]

omit [CompactSpace M] in
lemma restore_localize (i : A.centers) (f : M → V) (x : M) :
    restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f) x =
      (A.weight i x) ^ 2 • f x := by
  by_cases hx : x ∈ (chart (i : M)).source
  · rw [restore, indicator_of_mem hx, localize_chart _ _ _ hx]
    by_cases hzero : A.weight i x = 0
    · simp only [hzero, zero_pow (by decide : 2 ≠ 0), zero_smul, smul_zero]
    · rw [A.outer_one i x (subset_tsupport _ hzero), one_smul]
  · have hz : A.weight i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (A.weight_support i h))
    simp only [restore, indicator_of_notMem hx, hz, zero_pow (by decide : 2 ≠ 0), zero_smul]

omit [CompactSpace M] in
lemma sum_restore_localize (f : M → V) :
    (∑ i : A.centers, restore (i : M) (A.outer i) (localize (i : M) (A.weight i) f)) = f := by
  funext x
  simp only [Finset.sum_apply, A.restore_localize]
  rw [← Finset.sum_smul, A.partition, one_smul]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedCompositionBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth cutoff and chart transition operators preserve weighted
norms with constants independent of the input and its scale. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set WeightedEstimates
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A compactly supported coordinate change costs a fixed constant in each
weighted derivative norm; it introduces no additional scale loss. -/
theorem compact_localized_composition_bound {O K : Set Base}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχK : tsupport χ ⊆ K)
    {T : Base → Base} (hT : ContDiffOn ℝ ∞ T O) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedBound Set.univ s m C f →
      WeightedBound Set.univ s m (D * C) (fun x => χ x • f (T x)) := by
  obtain ⟨U, hU, hKU, hUO, hUc⟩ := exists_open_between_and_isCompact_closure hK hO hKO
  have hsub : U ⊆ O := subset_closure.trans hUO
  obtain ⟨A, hA, hbA⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hχ.contDiffOn m
  obtain ⟨B, hB, hbB⟩ := compact_coefficient_bound hO.uniqueDiffOn hUc hUO hT m
  refine ⟨2 ^ m * A * ((m.factorial : ℝ) * B ^ m), by positivity, ?_⟩
  intro f s C hs hs1 hC hf hb
  have hTj : ∀ j, 1 ≤ j → j ≤ m → ∀ x ∈ U,
      ‖iteratedFDerivWithin ℝ j T U x‖ ≤ B := by
    intro j _ hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) T x :=
      (hT.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hO.mem_nhds (hsub hx))
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbB j hj x (subset_closure hx)
    rwa [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
  have hχb : WeightedBound U s m A χ := by
    intro j hj x hx
    have ht : ContDiffAt ℝ (j : ℕ∞ω) χ x := (hχ.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx]
    have h := hbA j hj x (subset_closure hx)
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn ht (hsub hx)] at h
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs.le hs1)).trans h
  have hc := hb.comp_coordinates hU.uniqueDiffOn uniqueDiffOn_univ hs hs1 hB hC
    (hT.mono hsub) hf.contDiffOn (fun _ _ => mem_univ _) hTj
  have hcomp : ContDiffOn ℝ ∞ (fun x => f (T x)) U :=
    hf.contDiffOn.comp (hT.mono hsub) (fun _ _ => mem_univ _)
  have hp := hχb.smul_real hU.uniqueDiffOn hs.le (zero_le_one.trans hA)
    (by positivity) hχ.contDiffOn hcomp hc
  have hlocal : ContDiffOn ℝ ∞ (fun x => χ x • f (T x)) U := hχ.contDiffOn.smul hcomp
  intro j hj x _
  rw [iteratedFDerivWithin_univ]
  by_cases hx : x ∈ U
  · have ht : ContDiffAt ℝ (j : ℕ∞ω) (fun x => χ x • f (T x)) x :=
      (hlocal.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt (hU.mem_nhds hx)
    have h := hp j hj x hx
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn ht hx] at h
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  · have hxK : x ∉ K := fun hk => hx (hKU hk)
    have hxχ : x ∉ tsupport χ := fun hx' => hxK (hχK hx')
    have heq : (fun y => χ y • f (T y)) =ᶠ[𝓝 x] (fun _ => (0 : V)) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxχ] with y hy
      simp only [Pi.zero_apply] at hy
      rw [hy, zero_smul]
    have hd := (heq.iteratedFDeriv ℝ j).self_of_nhds
    rw [hd]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    positivity

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasWeightedBounds
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-atlas weighted norms and bounds for the actual restoration operator. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [IsManifold planeModel ∞ M] in
lemma localize_sum {ι : Type*} (b : Finset ι) (p : M) (ψ : M → ℝ) (f : ι → M → V) :
    localize p ψ (∑ i ∈ b, f i) = fun x => ∑ i ∈ b, localize p ψ (f i) x := by
  funext x
  by_cases hx : x ∈ (chart p).target <;>
    simp [localize, hx, Finset.sum_apply, Finset.smul_sum]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas bounds for the genuine smooth coordinate representatives.
The constants precede the map and scale, and no derivative order is lost. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma localize_outer_restore (i j : A.centers) (f : JetPolynomial.Base → V) :
    localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f) =
      fun x => localize (i : M) (A.outer i) (A.outer j) x •
        f (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize,restore,indicator_of_mem hi,indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hj (A.outer_support j h))
      simp only [localize,restore,indicator_of_mem hi,indicator_of_notMem hj,hz,smul_zero,zero_smul]
  · simp only [localize,indicator_of_notMem hi,zero_smul]

lemma localize_outer_restore_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C)
        (localize (i : M) (A.outer i) (restore (j : M) (A.outer j) f)) := by
  let K := (chart (i : M)) '' (tsupport (A.outer i) ∩ tsupport (A.outer j))
  have hK : IsCompact K :=
    ((isClosed_tsupport _).inter (isClosed_tsupport _)).isCompact.image_of_continuousOn
      ((chart (i : M)).continuousOn.mono (fun _ h => A.outer_support i h.1))
  have hKO : K ⊆ (transition (i : M) (j : M)).source := by
    rintro x ⟨p,hp,rfl⟩
    refine ⟨(chart (i : M)).map_source (A.outer_support i hp.1),?_⟩
    change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
    rw [(chart (i : M)).left_inv (A.outer_support i hp.1)]
    exact A.outer_support j hp.2
  obtain ⟨D,hD,hd⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source hK hKO
    (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i) (A.outer_smooth j))
    (localize_tsupport_inter (i : M) (A.outer_support i) (A.outer j))
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D,hD,?_⟩
  intro f s C hs hs1 hC hf hb
  rw [A.localize_outer_restore]
  exact hd f s C hs hs1 hC hf hb

theorem vectorChartRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorChartRead i F) := by
  classical
  choose D hD hd using fun j : A.centers => A.localize_outer_restore_bound (V := V) i j m
  refine ⟨∑ j : A.centers, D j,Finset.sum_nonneg (fun j _ => hD j),?_⟩
  intro F s C hs hs1 hC hF hb
  have he : A.vectorChartRead i F = fun x => ∑ j : A.centers,
      localize (i : M) (A.outer i)
        (restore (j : M) (A.outer j) (localize (j : M) (A.weight j) F)) x := by
    unfold vectorChartRead
    conv_lhs => rw [← A.sum_restore_localize F]
    exact localize_sum Finset.univ _ _ _
  rw [he,Finset.sum_mul]
  apply WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
  · intro j _
    exact (localize_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j)
        (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF))).contDiffOn
  · intro j _
    exact hd j _ s C hs hs1 hC
      (localize_smooth (j : M) (A.weight_smooth j) (A.weight_support j) hF) (hb j)

end SmoothingAtlas
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
local instance curvedPrimitiveFiberNormed_r66fe94_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance curvedPrimitiveFiberSpace_r66fe94_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance curvedPrimitiveDualAdd_r66fe94_1 : ∀ p : M,
    ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance curvedPrimitiveDualSmul_r66fe94_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M) (P : A.centers → JetPolynomial.Base → PhaseBasis)
  (u : ∀ p : M, CovariantTwoTensor p)

local instance curvedPrimitiveSectionNormed_r66fe94_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance curvedPrimitiveSectionSpace_r66fe94_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveFrameBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact bounds for actual coefficient and differential fields in the
fixed tensor frames, including overlapping phase charts. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameBoundDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameBoundDualSmul
variable (B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameBoundFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.frameBoundFiberSpace
local instance frameBoundSectionNormed_r66fe94_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance frameBoundSectionSpace_r66fe94_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] [T2Space M] in
lemma coefficientFrame_coordChange
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source) :
    B.coefficientFrame P i a p =
      ((P a.1 (chart (a.1 : M) p)).Q a.2).comp (fiberToThree.comp
        ((B.tensorTriv i).coordChangeL ℝ (B.tensorTriv a.1) p : TensorFiber →L[ℝ] TensorFiber)) := by
  apply ContinuousLinearMap.ext
  intro H
  change (P a.1 (chart (a.1 : M) p)).Q a.2
      (fiberToThree ((B.tensorTriv a.1).continuousLinearMapAt ℝ p
        ((B.tensorTriv i).symmL ℝ p H))) = _
  rw [(B.tensorTriv a.1).continuousLinearMapAt_apply_of_mem ℝ (B.tensorTriv_domain a.1 ha),
    (B.tensorTriv i).symmL_apply (R := ℝ) (B.tensorTriv_domain i hi),
    ← (B.tensorTriv i).coordChangeL_apply (R := ℝ) (B.tensorTriv a.1)
      ⟨B.tensorTriv_domain i hi,B.tensorTriv_domain a.1 ha⟩]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveCoefficientCoordinates
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! First-derivative bounds for coefficient functionals in each overlapping
primitive chart, fixed before choosing any independent phases or radii. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberNormed
local instance coefficientReadDerivativeNormed_r66fe94_1 : NormedAddCommGroup
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeSpace_r66fe94_1 : NormedSpace ℝ
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadPairNormed_r66fe94_1 : NormedAddCommGroup
    ((TensorFiber →L[ℝ] ℝ) × (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ)) := inferInstance
local instance coefficientReadDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.coefficientReadFiberNormed
local instance coefficientReadDerivativeNormed_r66fe94_2 : NormedAddCommGroup
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadDerivativeSpace_r66fe94_2 : NormedSpace ℝ
    (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ) := inferInstance
local instance coefficientReadPairNormed_r66fe94_2 : NormedAddCommGroup
    ((TensorFiber →L[ℝ] ℝ) × (JetPolynomial.Base →L[ℝ] TensorFiber →L[ℝ] ℝ)) := inferInstance
local instance coefficientReadDualSmul_r66fe94_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
variable (B : SmoothingAtlas M)

local instance coefficientReadSectionNormed_r66fe94_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance coefficientReadSectionSpace_r66fe94_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma coefficientFrame_smoothAt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source)
    (hQ : ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] ℝ) ∞ (B.coefficientFrame P i a) p := by
  have hq := hQ.contMDiffAt.comp p
    ((chart_smooth (a.1 : M) p ha).contMDiffAt ((chart (a.1 : M)).open_source.mem_nhds ha))
  have hT := (contMDiffOn_coordChangeL (IB := planeModel) (n := ∞)
    (B.tensorTriv i) (B.tensorTriv a.1)).contMDiffAt
    ((B.tensorTriv i).open_baseSet.inter (B.tensorTriv a.1).open_baseSet |>.mem_nhds
      ⟨B.tensorTriv_domain i hi,B.tensorTriv_domain a.1 ha⟩)
  have hconst : ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] PhaseMean.Tensor) ∞
      (fun _ : M => fiberToThree) p := contMDiffAt_const
  apply (hq.clm_comp (hconst.clm_comp hT)).congr_of_eventuallyEq
  filter_upwards [((chart (i : M)).open_source.inter (chart (a.1 : M)).open_source).mem_nhds
    ⟨hi,ha⟩] with q hq
  exact B.coefficientFrame_coordChange P i a hq.1 hq.2

omit [CompactSpace M] in
lemma coefficientFrameRead_smoothAt
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∈ (chart (a.1 : M)).source)
    (hQ : ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ContDiffAt ℝ ∞ (B.coefficientFrameRead P i a) (chart (i : M) p) := by
  have hx := (chart (i : M)).map_source hi
  have hsym := ((chart_symm_smooth (i : M)) _ hx).contMDiffAt
    ((chart (i : M)).open_target.mem_nhds hx)
  have hout : ContMDiffAt planeModel 𝓘(ℝ,TensorFiber →L[ℝ] ℝ) ∞
      (B.coefficientFrame P i a) ((chart (i : M)).symm (chart (i : M) p)) := by
    rw [(chart (i : M)).left_inv hi]
    exact B.coefficientFrame_smoothAt P i a hi ha hQ
  have h := hout.comp (chart (i : M) p) hsym
  exact h.contDiffAt

 theorem coefficientFrameRead_C1_bound
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (hQ : ∀ (a : B.centers × Fin 3) p, p ∈ tsupport (B.weight a.1) →
      ContDiffAt ℝ ∞ (fun y => (P a.1 y).Q a.2) (chart (a.1 : M) p)) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ i a p,
      p ∈ tsupport (B.weight i) → p ∈ tsupport (B.weight a.1) →
      ‖B.coefficientFrameRead P i a (chart (i : M) p)‖ ≤ D ∧
      ‖fderiv ℝ (B.coefficientFrameRead P i a) (chart (i : M) p)‖ ≤ D := by
  have hb (i : B.centers) (a : B.centers × Fin 3) : ∃ D : ℝ, 1 ≤ D ∧
      ∀ p ∈ tsupport (B.weight i) ∩ tsupport (B.weight a.1),
        ‖B.coefficientFrameRead P i a (chart (i : M) p)‖ ≤ D ∧
        ‖fderiv ℝ (B.coefficientFrameRead P i a) (chart (i : M) p)‖ ≤ D := by
    let K := (chart (i : M)) '' (tsupport (B.weight i) ∩ tsupport (B.weight a.1))
    have hK : IsCompact K := ((isClosed_tsupport (B.weight i)).inter
      (isClosed_tsupport (B.weight a.1))).isCompact.image_of_continuousOn
        ((chart (i : M)).continuousOn.mono (fun _ hp => B.weight_support i hp.1))
    have hc : ContinuousOn (fun y => (B.coefficientFrameRead P i a y,
        fderiv ℝ (B.coefficientFrameRead P i a) y)) K := by
      rintro y ⟨p,hp,rfl⟩
      have hs := B.coefficientFrameRead_smoothAt P i a (B.weight_support i hp.1)
        (B.weight_support a.1 hp.2) (hQ a p hp.2)
      exact (hs.continuousAt.prodMk (hs.continuousAt_fderiv (by simp))).continuousWithinAt
    obtain ⟨D,hD⟩ := hK.exists_bound_of_continuousOn hc
    refine ⟨max 1 D,le_max_left _ _,?_⟩
    intro p hp
    have hh := (hD _ ⟨p,hp,rfl⟩).trans (le_max_right 1 D)
    exact ⟨(norm_fst_le _).trans hh,(norm_snd_le _).trans hh⟩
  choose D hD hb using fun k : B.centers × (B.centers × Fin 3) => hb k.1 k.2
  refine ⟨1+∑ k, D k,?_,?_⟩
  · have := Finset.sum_nonneg (s := Finset.univ) (fun k _ => zero_le_one.trans (hD k))
    linarith
  · intro i a p hi ha
    have hle : D (i,a) ≤ 1+∑ k, D k := by
      have := Finset.single_le_sum (fun k _ => zero_le_one.trans (hD k)) (Finset.mem_univ (i,a))
      linarith
    exact ⟨((hb (i,a) p ⟨hi,ha⟩).1).trans hle,((hb (i,a) p ⟨hi,ha⟩).2).trans hle⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateC1Bounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed atlas seminorms control ordinary values and first derivatives on
all the original compact chart supports. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

theorem coordinate_C1_bound {D : ℝ} (hD : 0 ≤ D) :
    ∃ E : ℝ, 1 ≤ E ∧ ∀ F : M → V, ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      B.WeightedBound 1 1 D F → ∀ i p, p ∈ tsupport (B.weight i) →
        ‖F p‖ ≤ E ∧ ‖fderiv ℝ (F ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ E := by
  classical
  choose R hR hread using fun i : B.centers => B.vectorChartRead_bound (V := V) i 1
  let E := 1+(∑ i, R i)*D
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ => hR i)
  have hE : 1 ≤ E := by
    dsimp only [E]
    linarith [mul_nonneg hsum hD]
  refine ⟨E,hE,?_⟩
  intro F hF hb i p hp
  have h := hread i F 1 D zero_lt_one le_rfl hD hF hb
  have hi : R i*D ≤ E := by
    have hh := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun j _ => hR j) (Finset.mem_univ i)) hD
    dsimp only [E]
    linarith
  have hv := (h.norm_le (mem_univ (chart (i : M) p))).trans hi
  rw [B.vectorChartRead_on_support i F ⟨p,hp,rfl⟩,
    (chart (i : M)).left_inv (B.weight_support i hp)] at hv
  refine ⟨hv,?_⟩
  have hd := h.deriv_le zero_lt_one le_rfl (mem_univ (chart (i : M) p))
  simp only [iteratedFDerivWithin_univ,one_pow,div_one,norm_iteratedFDeriv_one] at hd
  rw [B.vectorChartRead_fderiv i hF ⟨p,hp,rfl⟩] at hd
  exact hd.trans hi

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCoordinateCovector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The first phase coordinate has the exact covector used by the local
rank-one tensor pullback. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4
open SurfaceJetCoordinates

namespace FiniteOrderSmoothing.SmoothingAtlas
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
variable (A : SmoothingAtlas M)

lemma jetChart_tangentCoordinates (i : A.centers) {p : M}
    (hp : p ∈ (chart (i : M)).source) :
    mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base) (chart (i : M)) p =
      (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap.comp
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p) := by
  have hp' : p ∈ (chartAt Plane (i : M)).source := by simpa only [chart_source] using hp
  have hc := (contMDiffOn_chart (I := planeModel) (n := ∞) (x := (i : M)) p hp').contMDiffAt
    ((chartAt Plane (i : M)).open_source.mem_nhds hp')
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hp']
  change mfderiv planeModel 𝓘(ℝ,JetPolynomial.Base)
    ((EuclideanSpace.equiv (Fin 2) ℝ) ∘ chartAt Plane (i : M)) p = _
  rw [mfderiv_comp p
    (((EuclideanSpace.equiv (Fin 2) ℝ).contDiff (n := (∞ : ℕ∞ω))).contMDiff.mdifferentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).mdifferentiableAt
    (hc.mdifferentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),mfderiv_eq_fderiv,
    (EuclideanSpace.equiv (Fin 2) ℝ).fderiv]
  rfl

end FiniteOrderSmoothing.SmoothingAtlas
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCovectorRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual covector in a tangent frame is the derivative of the
scalar phase in that chart. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

lemma covectorFrame_mfderiv (phi : M → ℝ) (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi)
    (i : B.centers) {p : M} (hp : p ∈ (chart (i : M)).source) :
    B.covectorFrame i p (mfderiv planeModel 𝓘(ℝ) phi p) =
      (fderiv ℝ (phi ∘ (chart (i : M)).symm) (chart (i : M) p)).comp
        (EuclideanSpace.equiv (Fin 2) ℝ).toContinuousLinearMap := by
  let f := phi ∘ (chart (i : M)).symm
  have hf : ContDiffOn ℝ ∞ f (chart (i : M)).target :=
    (hphi.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  have hx := (chart (i : M)).map_source hp
  have hfa := hf.contDiffAt ((chart (i : M)).open_target.mem_nhds hx)
  have hc := ((chart_smooth (i : M)) p hp).contMDiffAt
    ((chart (i : M)).open_source.mem_nhds hp)
  have he : phi =ᶠ[𝓝 p] (f ∘ chart (i : M)) := by
    filter_upwards [(chart (i : M)).open_source.mem_nhds hp] with q hq
    exact congrArg phi ((chart (i : M)).left_inv hq).symm
  have hd := he.mfderiv_eq (I := planeModel) (I' := 𝓘(ℝ))
  erw [mfderiv_comp p (hfa.contMDiffAt.mdifferentiableAt (by simp))
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv,B.jetChart_tangentCoordinates i hp] at hd
  have ht : p ∈ (trivializationAt Plane (TangentSpace planeModel) (i : M)).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet,chart_source] using hp
  apply ContinuousLinearMap.ext
  intro v
  change (mfderiv planeModel 𝓘(ℝ) phi p)
    ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v) = _
  rw [hd]
  change fderiv ℝ f (chart (i : M) p)
      ((EuclideanSpace.equiv (Fin 2) ℝ)
        ((trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt ℝ p
          ((trivializationAt Plane (TangentSpace planeModel) (i : M)).symmL ℝ p v))) = _
  rw [(trivializationAt Plane (TangentSpace planeModel) (i : M)).continuousLinearMapAt_symmL ht]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactParameterC1
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact C1 bounds for a smooth parameter family and its spatial slices. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {P X V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem compact_parameter_C1 {A : Set P} {K : Set X} (hA : IsCompact A) (hK : IsCompact K)
    {F : P × X → V} (hF : ∀ z ∈ A ×ˢ K, ContDiffAt ℝ ∞ F z) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ a ∈ A, ∀ x ∈ K,
      ‖F (a,x)‖ ≤ D ∧ ‖fderiv ℝ (fun y => F (a,y)) x‖ ≤ D := by
  have hc : ContinuousOn (fun z => (F z,fderiv ℝ F z)) (A ×ˢ K) := by
    intro z hz
    exact ((hF z hz).continuousAt.prodMk ((hF z hz).continuousAt_fderiv (by simp))).continuousWithinAt
  obtain ⟨C,hC⟩ := (hA.prod hK).exists_bound_of_continuousOn hc
  refine ⟨max 1 C,le_max_left _ _,?_⟩
  intro a ha x hx
  have hb := (hC (a,x) ⟨ha,hx⟩).trans (le_max_right 1 C)
  have hv := (norm_fst_le (F (a,x),fderiv ℝ F (a,x))).trans hb
  have hd := (norm_snd_le (F (a,x),fderiv ℝ F (a,x))).trans hb
  refine ⟨hv,?_⟩
  have hpair : HasFDerivAt (fun y : X => (a,y)) (ContinuousLinearMap.inr ℝ P X) x :=
    (hasFDerivAt_const a x).prodMk (hasFDerivAt_id x)
  have he := ((hF (a,x) ⟨ha,hx⟩).differentiableAt (by simp)).hasFDerivAt.comp x hpair
  change ‖fderiv ℝ (F ∘ Prod.mk a) x‖ ≤ max 1 C
  rw [he.fderiv]
  calc
    _ ≤ ‖fderiv ℝ F (a,x)‖*‖ContinuousLinearMap.inr ℝ P X‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ F (a,x)‖*1 := mul_le_mul_of_nonneg_left
      (ContinuousLinearMap.norm_inr_le_one ℝ P X) (norm_nonneg _)
    _ ≤ max 1 C := by simpa only [mul_one] using hd

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularPhaseDependence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact affine dependence of supported circular phases on their linear
parameters. The curvature parameter stays fixed. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open PhaseGeometry SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_smooth (i : B.centers) (ell : Base) (L : ℝ) :
    ContMDiff planeModel 𝓘(ℝ) ∞ (B.circularPhase i ell L) :=
  restore_smooth (i : M) (B.outer_smooth i) (B.outer_support i)
    ((centeredConvexPhase_smooth _ _ _).comp JetPolynomial.planeCoordinateIsometry.contDiff)

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_sub (i : B.centers) (ell ell₀ : Base) (L : ℝ) :
    B.circularPhase i ell L-B.circularPhase i ell₀ L =
      (ell.1-ell₀.1) • B.circularPhase i (1,0) 0+
        (ell.2-ell₀.2) • B.circularPhase i (0,1) 0 := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [circularPhase,restore,hp,indicator_of_mem,Function.comp_apply,
      Pi.sub_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul,centeredConvexPhase,
      convexQuadraticPhase,phaseLinear,Prod.fst_sub,Prod.snd_sub,
      add_apply,smul_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd']
    ring
  · simp only [circularPhase,restore,indicator_of_notMem hp,Pi.sub_apply,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul,sub_self,mul_zero,add_zero]

omit [CompactSpace M] [T2Space M] in
lemma circularPhase_mfderiv_sub (i : B.centers) (ell ell₀ : Base) (L : ℝ) (p : M) :
    (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
      (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell₀ L) p) =
      (ell.1-ell₀.1) • (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)+
        (ell.2-ell₀.2) • (show Plane →L[ℝ] ℝ from mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p) := by
  have h1 := ((B.circularPhase_smooth i ell L) p).mdifferentiableAt (by simp)
  have h0 := ((B.circularPhase_smooth i ell₀ L) p).mdifferentiableAt (by simp)
  have hx := ((B.circularPhase_smooth i (1,0) 0) p).mdifferentiableAt (by simp)
  have hy := ((B.circularPhase_smooth i (0,1) 0) p).mdifferentiableAt (by simp)
  erw [← mfderiv_sub h1 h0,B.circularPhase_sub]
  erw [mfderiv_add (hx.const_smul _) (hy.const_smul _),
    const_smul_mfderiv hx,const_smul_mfderiv hy]
  rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseCovectorFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact parameter bounds for the actual circular phase differentials,
including their first spatial derivatives. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open SmallModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

omit [CompactSpace M] [T2Space M] in
lemma phaseCovectorRead_smoothOn (i : B.centers) (phi : M → ℝ)
    (hphi : ContMDiff planeModel 𝓘(ℝ) ∞ phi) :
    ContDiffOn ℝ ∞ (B.phaseCovectorRead i phi) (chart (i : M)).target := by
  have h := (hphi.comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  exact (h.fderiv_of_isOpen (chart (i : M)).open_target (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_comp contDiffOn_const

omit [CompactSpace M] [T2Space M] in
lemma circularCovectorJoint_smoothOn (i j : B.centers) (L : ℝ) :
    ContDiffOn ℝ ∞ (B.circularCovectorJoint i j L)
      (univ ×ˢ (chart (j : M)).target) := by
  have h0 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i 0 L)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have h1 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i (1,0) 0)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have h2 := (B.phaseCovectorRead_smoothOn j _ (B.circularPhase_smooth i (0,1) 0)).comp
    (contDiffOn_snd : ContDiffOn ℝ ∞ (fun z : Base × JetPolynomial.Base => z.2)
      (univ ×ˢ (chart (j : M)).target))
    (fun (_ : Base × JetPolynomial.Base) (hz : _ ∈ univ ×ˢ (chart (j : M)).target) => hz.2)
  have he1 : ContDiff ℝ ∞ (fun z : Base × JetPolynomial.Base => z.1.1) := contDiff_fst.fst
  have he2 : ContDiff ℝ ∞ (fun z : Base × JetPolynomial.Base => z.1.2) := contDiff_fst.snd
  exact (h0.add (he1.contDiffOn.smul h1)).add (he2.contDiffOn.smul h2)

omit [CompactSpace M] [T2Space M] in
lemma circularCovectorJoint_eq (i j : B.centers) (ell : Base) (L : ℝ)
    {y : JetPolynomial.Base} (hy : y ∈ (chart (j : M)).target) :
    B.phaseCovectorRead j (B.circularPhase i ell L) y = B.circularCovectorJoint i j L (ell,y) := by
  let p := (chart (j : M)).symm y
  have hp : p ∈ (chart (j : M)).source := (chart (j : M)).map_target hy
  have hpy : chart (j : M) p = y := (chart (j : M)).right_inv hy
  have h := B.circularPhase_mfderiv_sub i ell 0 L p
  have hh := congrArg (fun v : Plane →L[ℝ] ℝ => B.covectorFrame j p v) h
  unfold covectorFrame at hh
  erw [ContinuousLinearMap.sub_comp,ContinuousLinearMap.add_comp,
    ContinuousLinearMap.smul_comp,ContinuousLinearMap.smul_comp] at hh
  change B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i ell L) p)-
      B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i 0 L) p) =
    (ell.1-0) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (1,0) 0) p)+
    (ell.2-0) • B.covectorFrame j p (mfderiv planeModel 𝓘(ℝ) (B.circularPhase i (0,1) 0) p) at hh
  rw [B.covectorFrame_mfderiv _ (B.circularPhase_smooth i ell L) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i 0 L) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i (1,0) 0) j hp,
    B.covectorFrame_mfderiv _ (B.circularPhase_smooth i (0,1) 0) j hp,hpy] at hh
  change B.phaseCovectorRead j (B.circularPhase i ell L) y-
      B.phaseCovectorRead j (B.circularPhase i 0 L) y =
    (ell.1-0) • B.phaseCovectorRead j (B.circularPhase i (1,0) 0) y+
    (ell.2-0) • B.phaseCovectorRead j (B.circularPhase i (0,1) 0) y at hh
  simp only [sub_zero] at hh
  have hh' := congrArg (fun v => v+B.phaseCovectorRead j (B.circularPhase i 0 L) y) hh
  rw [sub_add_cancel] at hh'
  rw [hh']
  unfold circularCovectorJoint
  abel

omit [T2Space M] in
theorem circular_covector_parameter_bound (i j : B.centers) (L : ℝ)
    {P : Set Base} (hP : IsCompact P) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ ell ∈ P, ∀ y ∈ (B.chartWeightCompact j : Set JetPolynomial.Base),
      ‖B.phaseCovectorRead j (B.circularPhase i ell L) y‖ ≤ D ∧
      ‖fderiv ℝ (B.phaseCovectorRead j (B.circularPhase i ell L)) y‖ ≤ D := by
  have hK := (B.chartWeightCompact j).isCompact
  have hsub : (B.chartWeightCompact j : Set JetPolynomial.Base) ⊆ (chart (j : M)).target := by
    rintro y ⟨p,hp,rfl⟩
    exact (chart (j : M)).map_source (B.weight_support j hp)
  have hj := B.circularCovectorJoint_smoothOn i j L
  obtain ⟨D,hD,hbound⟩ := compact_parameter_C1 hP hK
    (fun z hz => hj.contDiffAt ((isOpen_univ.prod (chart (j : M)).open_target).mem_nhds
      ⟨mem_univ _,hsub hz.2⟩))
  refine ⟨D,hD,?_⟩
  intro ell hell y hy
  have he : B.phaseCovectorRead j (B.circularPhase i ell L) =ᶠ[𝓝 y]
      (fun x => B.circularCovectorJoint i j L (ell,x)) := by
    filter_upwards [(chart (j : M)).open_target.mem_nhds (hsub hy)] with x hx
    exact B.circularCovectorJoint_eq i j ell L hx
  rw [he.self_of_nhds,he.fderiv_eq]
  exact hbound ell hell y hy

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_ReferencePhaseC1
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed first-jet budget for every phase in the reference parameter balls. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace ReferenceCircularAtlas
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

theorem perturbed_phase_C1_bound : ∃ D : ℝ, 1 ≤ D ∧
    ∀ ell : d.B.centers → Fin 3 → SmallModes.Base,
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ ≤ 1) →
      ∀ (i : d.B.centers) (a : d.B.centers × Fin 3) p,
      p ∈ tsupport (d.B.weight i) →
        ‖d.B.phaseCovectorRead i (d.perturbedPhases ell a) (chart (i : M) p)‖ ≤ D ∧
        ‖fderiv ℝ (d.B.phaseCovectorRead i (d.perturbedPhases ell a)) (chart (i : M) p)‖ ≤ D := by
  classical
  choose D hD hbound using fun k : d.B.centers × (d.B.centers × Fin 3) =>
    d.B.circular_covector_parameter_bound k.2.1 k.1 (d.L k.2.1)
      (isCompact_closedBall ((d.P k.2.1).ξ k.2.2) 1)
  let E := 1+∑ k, D k
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun k _ => zero_le_one.trans (hD k))
  refine ⟨E,by dsimp only [E] <;> linarith,?_⟩
  intro ell hell i a p hp
  have he : ell a.1 a.2 ∈ Metric.closedBall ((d.P a.1).ξ a.2) 1 := by
    simpa only [Metric.mem_closedBall,dist_eq_norm] using hell a.1 a.2
  have h := hbound (i,a) (ell a.1 a.2) he (chart (i : M) p) ⟨p,hp,rfl⟩
  have hle : D (i,a) ≤ E := by
    have hh := Finset.single_le_sum (fun k _ => zero_le_one.trans (hD k)) (Finset.mem_univ (i,a))
    dsimp only [E] <;> linarith
  exact ⟨h.1.trans hle,h.2.trans hle⟩

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveAmplitudeZero
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Outside its original chart support the actual amplitude has zero first jet. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]
namespace SmoothingAtlas
variable (B : SmoothingAtlas M)

lemma correctedAmplitude_zero_coordinate
    (P : B.centers → JetPolynomial.Base → PhaseGeometry.PhaseBasis)
    (psi phi : (B.centers × Fin 3) → M → ℝ)
    (u : ∀ p : M, CovariantTwoTensor p)
    (hs : ∀ a, tsupport (psi a) ⊆ tsupport (B.weight a.1))
    (i : B.centers) (a : B.centers × Fin 3) {p : M}
    (hi : p ∈ (chart (i : M)).source) (ha : p ∉ tsupport (B.weight a.1)) :
    B.correctedPrimitiveAmplitude P psi phi u a p = 0 ∧
      fderiv ℝ (B.correctedPrimitiveAmplitude P psi phi u a ∘ (chart (i : M)).symm)
        (chart (i : M) p) = 0 := by
  have hn : p ∉ tsupport (B.correctedPrimitiveAmplitude P psi phi u a) := by
    intro hp
    exact ha (hs a (tsupport_mul_subset_left hp))
  have hz := notMem_tsupport_iff_eventuallyEq.mp hn
  have hc : Tendsto (chart (i : M)).symm (𝓝 (chart (i : M) p)) (𝓝 p) := by
    have h := ((chart (i : M)).continuousOn_symm _ ((chart (i : M)).map_source hi)).continuousAt
      ((chart (i : M)).open_target.mem_nhds ((chart (i : M)).map_source hi))
    simpa only [(chart (i : M)).left_inv hi] using h.tendsto
  have he : (B.correctedPrimitiveAmplitude P psi phi u a ∘ (chart (i : M)).symm) =ᶠ[𝓝 (chart (i : M) p)]
      (fun _ => 0) := hz.comp_tendsto hc
  exact ⟨hz.self_of_nhds,(he.fderiv_eq (𝕜 := ℝ)).trans (fderiv_const_apply _)⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_UniformActualAmplitudeC1
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform first-derivative bounds for the genuine corrected amplitudes.
The tolerances and bounds precede all later finite cycles and boundary choices. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberAdd
local instance actualC1TensorDualNormed_r66fe94_1 : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1TensorDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1CovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1CovectorSpace
local instance actualC1FiberT2_r66fe94_1 : T2Space TensorFiber := inferInstance
local instance actualC1TensorDualT2_r66fe94_1 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorT2_r66fe94_1 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1DataNormed_r66fe94_1 (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1DataSpace
local instance actualC1DataT2_r66fe94_1 (ι : Type*) [Fintype ι] : T2Space (PrimitiveAmplitudeData ι) := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M] [T2Space M]
local instance actualC1DataDualNormed_r66fe94_1 (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance actualC1DataDualSpace_r66fe94_1 (ι : Type*) [Fintype ι] : NormedSpace ℝ (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance actualC1DualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
local instance actualC1DualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) := fun _ => inferInstance
namespace ReferenceCircularAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1FiberAdd
local instance actualC1TensorDualNormed_r66fe94_2 : NormedAddCommGroup (TensorFiber →L[ℝ] ℝ) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1TensorDualSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1CovectorNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1CovectorSpace
local instance actualC1FiberT2_r66fe94_2 : T2Space TensorFiber := inferInstance
local instance actualC1TensorDualT2_r66fe94_2 : T2Space (TensorFiber →L[ℝ] ℝ) := inferInstance
local instance actualC1CovectorT2_r66fe94_2 : T2Space (Plane →L[ℝ] ℝ) := inferInstance
local instance actualC1DataNormed_r66fe94_2 (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι) := inferInstance
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.actualC1DataSpace
local instance actualC1DataT2_r66fe94_2 (ι : Type*) [Fintype ι] : T2Space (PrimitiveAmplitudeData ι) := inferInstance
variable {A : SmoothingAtlas M} {gref g : SmoothMetric M} {c C : ℝ}
  (d : ReferenceCircularAtlas A gref g c C)

local instance actualC1DataDualNormed_r66fe94_2 (ι : Type*) [Fintype ι] : NormedAddCommGroup (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance actualC1DataDualSpace_r66fe94_2 (ι : Type*) [Fintype ι] : NormedSpace ℝ (PrimitiveAmplitudeData ι →L[ℝ] ℝ) := inferInstance
local instance actualC1SectionNormed_r66fe94_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance actualC1SectionSpace_r66fe94_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem uniform_actual_amplitude_C1_oai {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (r : ℝ)
    (href : gref.inner = g.inner-inducedTensor (r • F)) :
    ∃ pt wt mt : ℝ, 0 < pt ∧ 0 < wt ∧ 0 < mt ∧
      ∀ Dw Du : ℝ, 0 ≤ Dw → 0 ≤ Du → ∃ E : ℝ, 1 ≤ E ∧
      ∀ (ell : d.B.centers → Fin 3 → SmallModes.Base) (psi : (d.B.centers × Fin 3) → M → ℝ),
      (∀ i j, ‖ell i j-(d.P i).ξ j‖ < pt) →
      (∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (psi a)) →
      (∀ a, tsupport (psi a) ⊆ tsupport (d.B.weight a.1)) →
      (∀ a p, |psi a p-d.B.weight a.1 p| < wt) →
      (∀ a, d.B.WeightedBound 1 1 Dw (psi a)) →
      ∀ G : M → Space, ContMDiff planeModel spaceModel ∞ G →
      A.WeightedBound 1 1 mt (G-F) →
      d.B.TensorWeightedBound 1 1 Du (g.inner-inducedTensor (r • G)) →
      ∀ i a p, p ∈ tsupport (d.B.weight i) →
      let amp := d.B.correctedPrimitiveAmplitude d.basis psi (d.perturbedPhases ell)
        (g.inner-inducedTensor (r • G)) a
      |amp p| ≤ E ∧ ‖fderiv ℝ (amp ∘ (chart (i : M)).symm) (chart (i : M) p)‖ ≤ E := by
  obtain ⟨pt,wt,mt,R,hpt,hwt,hmt,hR,hparam⟩ := d.actual_amplitude_parameter_bound hF r href
  refine ⟨min pt 1,wt,mt,lt_min hpt zero_lt_one,hwt,hmt,?_⟩
  intro Dw Du hDw hDu
  obtain ⟨Dq,hDq,hq⟩ := d.B.coefficientFrameRead_C1_bound d.basis
    (fun a _p hp => d.basis_smooth a.1 hp a.2)
  obtain ⟨W,hW,hw⟩ := d.B.coordinate_C1_bound (V := ℝ) hDw
  obtain ⟨V,hV,hv⟩ := d.perturbed_phase_C1_bound
  obtain ⟨H,hH,hHbound⟩ := d.B.tensorFrameRead_C1_bound hDu
  let D := Dq+W+V+H
  have hD : 0 ≤ D := by dsimp only [D] <;> linarith
  have hqD : Dq ≤ D := by dsimp only [D] <;> linarith
  have hWD : W ≤ D := by dsimp only [D] <;> linarith
  have hVD : V ≤ D := by dsimp only [D] <;> linarith
  have hHD : H ≤ D := by dsimp only [D] <;> linarith
  let E := R*(1+D)
  have hRE : R ≤ E := by dsimp only [E] <;> nlinarith
  have hDE : R*D ≤ E := by dsimp only [E] <;> nlinarith
  refine ⟨E,hR.trans hRE,?_⟩
  intro ell psi hell hpsi hs hclose hbpsi G hG hnear hbu i a p hp
  let u := g.inner-inducedTensor (r • G)
  let phi := d.perturbedPhases ell
  have hphi (b : d.B.centers × Fin 3) : ContMDiff planeModel 𝓘(ℝ) ∞ (phi b) :=
    d.B.curvedAtlasPhase_smooth (d.B.centeredPhaseFamily ell d.L)
      (fun _ _ => PhaseGeometry.centeredConvexPhase_smooth _ _ _) b
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
  have hell1 : ∀ i j, ‖ell i j-(d.P i).ξ j‖ ≤ 1 :=
    fun i j => (hell i j).le.trans (min_le_right _ _)
  by_cases ha : p ∈ tsupport (d.B.weight a.1)
  · have hd : ‖fderiv ℝ (d.B.primitiveCoordinateData d.basis psi phi u i
        {b | p ∈ tsupport (d.B.weight b.1)}) (chart (i : M) p)‖ ≤ D := by
      apply d.B.primitiveCoordinateData_fderiv_bound d.basis psi phi hpsi hphi
        (fun b _p hb => d.basis_smooth b.1 hb b.2) u hu i hp hD
      · intro b hb
        exact (hq i b p hp hb).2.trans hqD
      · intro b
        exact (hw (psi b) (hpsi b) (hbpsi b) i p hp).2.trans hWD
      · intro b _hb
        exact (hv ell hell1 i b p hp).2.trans hVD
      · exact (hHbound u hu hsym hbu i p hp).2.trans hHD
    have hpa := hparam ell psi (fun i j => (hell i j).trans_le (min_le_left _ _))
      hclose G hG hnear i p hp a ha
    have hh := d.B.correctedAmplitude_coordinate_bound d.basis psi phi hpsi hphi
      (fun b _p hb => d.basis_smooth b.1 hb b.2) hs u hu i hp a ha R D hd hpa
    exact ⟨hh.1.trans hRE,hh.2.trans hDE⟩
  · have hz := d.B.correctedAmplitude_zero_coordinate d.basis psi phi u hs i a
      (d.B.weight_support i hp) ha
    change |d.B.correctedPrimitiveAmplitude d.basis psi phi u a p| ≤ E ∧ _
    rw [hz.1,hz.2,abs_zero,norm_zero]
    exact ⟨zero_le_one.trans (hR.trans hRE),zero_le_one.trans (hR.trans hRE)⟩

end ReferenceCircularAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.ReferenceCircularAtlas.uniform_actual_amplitude_C1_oai.{u_1}
