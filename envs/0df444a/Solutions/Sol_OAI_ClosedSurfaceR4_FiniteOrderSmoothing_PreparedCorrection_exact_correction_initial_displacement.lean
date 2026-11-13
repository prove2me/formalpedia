-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:31:00.620167+00:00
-- url     : https://prove2.me/submissions/fcf1c8a5-dca8-4db3-8af3-7c9d9d172fe2

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010
import Definitions.Def_OAIQ249SI011

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

theorem vectorPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.WeightedBound s m C F →
      WeightedEstimates.WeightedBound univ s m (D*C) (A.vectorPlaneRead i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := V) i m
  refine ⟨D,hD,?_⟩
  intro F s C hs hs1 hC hF hb
  exact weightedBound_comp_isometry planeCoordinateIsometry.symm
    (A.vectorChartRead_smooth i hF) (hd F s C hs hs1 hC hF hb)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_OrderwiseCorrectionLimit
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.tensorTranspose_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth correction limits with a separate summable bound at each derivative order. -/
noncomputable section
open Filter Manifold
open scoped Topology ContDiff

namespace ClosedSurfaceR4.ExactCorrection

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

theorem smooth_limitMap_orderwise {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hρ : ∀ m, Summable (ρ m))
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ m n) :
    ContDiff ℝ ∞ (limitMap F U) := by
  apply hF.add
  apply contDiff_tsum_of_eventually (N := ⊤) hU (fun m _ => hρ m)
  intro m _
  simpa only [Nat.cofinite_eq_atTop] using hbound m

theorem hasFDerivAt_limitMap_orderwise
    {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hρ : ∀ m, Summable (ρ m))
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ m n) (x : E) :
    HasFDerivAt (limitMap F U)
      (fderiv ℝ F x + ∑' n, fderiv ℝ (U n) x) x := by
  have hb0 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E), ‖U n y‖ ≤ ρ 0 n := by
    filter_upwards [hbound 0] with n hn y _
    simpa only [norm_iteratedFDeriv_zero] using hn y
  have hb1 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E),
      ‖fderiv ℝ (U n) y‖ ≤ ρ 1 n := by
    filter_upwards [hbound 1] with n hn y _
    simpa only [norm_iteratedFDeriv_one] using hn y
  have hval := tendstoUniformlyOn_tsum_nat_eventually (hρ 0) hb0
  have hder := tendstoUniformlyOn_tsum_nat_eventually (hρ 1) hb1
  have hs : HasFDerivAt (fun y => ∑' n, U n y)
      (∑' n, fderiv ℝ (U n) x) x := by
    apply hasFDerivAt_of_tendstoUniformlyOn isOpen_univ hder
    · intro N y _
      exact HasFDerivAt.fun_sum fun n _ =>
        ((hU n).differentiable (by simp) y).hasFDerivAt
    · intro y hy
      exact hval.tendsto_at hy
    · exact Set.mem_univ x
  exact ((hF.differentiable (by simp) x).hasFDerivAt.add hs)

theorem tendsto_fderiv_partialMap_orderwise
    {F : E → V} {U : ℕ → E → V} {ρ : ℕ → ℕ → ℝ}
    (hF : ContDiff ℝ ∞ F) (hU : ∀ n, ContDiff ℝ ∞ (U n))
    (hρ : ∀ m, Summable (ρ m))
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (U n) x‖ ≤ ρ m n) (x : E) :
    Tendsto (fun N => fderiv ℝ (partialMap F U N) x) atTop
      (𝓝 (fderiv ℝ (limitMap F U) x)) := by
  have hb1 : ∀ᶠ n in atTop, ∀ y ∈ (Set.univ : Set E),
      ‖fderiv ℝ (U n) y‖ ≤ ρ 1 n := by
    filter_upwards [hbound 1] with n hn y _
    simpa only [norm_iteratedFDeriv_one] using hn y
  have hder := (tendstoUniformlyOn_tsum_nat_eventually (hρ 1) hb1).tendsto_at (Set.mem_univ x)
  have hfinite (N : ℕ) : fderiv ℝ (partialMap F U N) x =
      fderiv ℝ F x + ∑ n ∈ Finset.range N, fderiv ℝ (U n) x := by
    exact ((hF.differentiable (by simp) x).hasFDerivAt.add
      (HasFDerivAt.fun_sum fun n _ =>
        ((hU n).differentiable (by simp) x).hasFDerivAt)).fderiv
  simp_rw [hfinite]
  rw [(hasFDerivAt_limitMap_orderwise hF hU hρ hbound x).fderiv]
  exact tendsto_const_nhds.add hder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
/-- A representative in any smooth local coordinate map determines the actual
manifold derivative, with the fixed coordinate derivative as the right factor. -/
lemma local_coordinate_representative_derivative
    {c : M → E} {G : M → Space} {K : E → Space} (p : M)
    (hc : ContMDiffAt planeModel 𝓘(ℝ,E) ∞ c p) (hK : ContDiff ℝ ∞ K)
    (heq : G =ᶠ[𝓝 p] K ∘ c) :
    ContMDiffAt planeModel spaceModel ∞ G p ∧
      mfderiv planeModel spaceModel G p =
        (fderiv ℝ K (c p)).comp (mfderiv planeModel 𝓘(ℝ,E) c p) := by
  have hs : ContMDiffAt planeModel spaceModel ∞ (K ∘ c) p :=
    hK.contMDiff.contMDiffAt.comp p hc
  refine ⟨hs.congr_of_eventuallyEq heq,?_⟩
  have hd := heq.mfderiv_eq (I := planeModel) (I' := spaceModel)
  rw [mfderiv_comp p (hK.contMDiff.mdifferentiable (by simp)).mdifferentiableAt
    (hc.mdifferentiableAt (by simp)),mfderiv_eq_fderiv] at hd
  change (mfderiv planeModel spaceModel G p : Plane →L[ℝ] Space) =
    (ContinuousLinearMap.id ℝ Space).comp
      ((fderiv ℝ K (c p)).comp (mfderiv planeModel 𝓘(ℝ,E) c p)) at hd
  simpa only [ContinuousLinearMap.id_comp] using hd

omit [IsManifold planeModel ∞ M] in
/-- Local coordinate representatives with order-dependent summable tails give
smoothness of the series and convergence of the true manifold derivatives. -/
theorem local_coordinate_correction_limit
    {F : M → Space} {U : ℕ → M → Space} {c : M → E}
    {K : E → Space} {A : ℕ → E → Space} {ρ : ℕ → ℕ → ℝ} (p : M)
    (hc : ContMDiffAt planeModel 𝓘(ℝ,E) ∞ c p)
    (hK : ContDiff ℝ ∞ K) (hA : ∀ n, ContDiff ℝ ∞ (A n))
    (hρ : ∀ m, Summable (ρ m))
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop,
      ∀ x, ‖iteratedFDeriv ℝ m (A n) x‖ ≤ ρ m n)
    (heq : ∀ᶠ x in 𝓝 p, F x = K (c x) ∧ ∀ n, U n x = A n (c x)) :
    ContMDiffAt planeModel spaceModel ∞ (manifoldLimitMap F U) p ∧
      Tendsto (fun N => mfderiv planeModel spaceModel (manifoldPartialMap F U N) p) atTop
        (𝓝 (mfderiv planeModel spaceModel (manifoldLimitMap F U) p)) := by
  have hl : manifoldLimitMap F U =ᶠ[𝓝 p] limitMap K A ∘ c := by
    filter_upwards [heq] with x hx
    simp only [manifoldLimitMap,limitMap,Function.comp_apply,hx.1,hx.2]
  have hs := local_coordinate_representative_derivative p hc
    (smooth_limitMap_orderwise hK hA hρ hbound) hl
  refine ⟨hs.1,?_⟩
  have hf (N : ℕ) : mfderiv planeModel spaceModel (manifoldPartialMap F U N) p =
      (fderiv ℝ (partialMap K A N) (c p)).comp (mfderiv planeModel 𝓘(ℝ,E) c p) := by
    apply (local_coordinate_representative_derivative p hc
      (hK.add (ContDiff.sum (fun n _ => hA n))) ?_).2
    filter_upwards [heq] with x hx
    simp only [manifoldPartialMap,Function.comp_apply,hx.1,hx.2]
  simp_rw [hf,hs.2]
  let compose : (E →L[ℝ] Space) →L[ℝ] (Plane →L[ℝ] Space) :=
    (ContinuousLinearMap.compL ℝ Plane E Space).flip
      (mfderiv planeModel 𝓘(ℝ,E) c p)
  exact (compose.continuous.tendsto _).comp
    (tendsto_fderiv_partialMap_orderwise hK hA hρ hbound (c p))

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasCorrectionLimit
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual fixed-atlas correction bounds imply a smooth manifold limit
and convergence of the manifold differentials. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates
open ExactCorrection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- Every point is seen by at least one genuine partition weight. -/
lemma exists_weight_ne_zero (p : M) : ∃ i : A.centers, A.weight i p ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have hp := A.partition p
  simp only [h,zero_pow (by decide : 2 ≠ 0),Finset.sum_const_zero] at hp
  norm_num at hp

omit [CompactSpace M] in
/-- Where its outer cutoff is one, the coordinate representative agrees
with the original map, for every map simultaneously. -/
lemma vectorPlaneRead_coordinateChart_of_outer_one (i : A.centers) (V : M → Space)
    {x : M} (hx : x ∈ (chart (i : M)).source) (ho : A.outer i x = 1) :
    V x = A.vectorPlaneRead i V (coordinateChart (i : M) x) := by
  change V x = localize (i : M) (A.outer i) V
    (planeCoordinateIsometry.symm (planeCoordinateIsometry (chart (i : M) x)))
  rw [LinearIsometryEquiv.symm_apply_apply,localize_chart _ _ _ hx,ho,one_pow,one_smul]

/-- The global atlas norm can be used directly; the summable bound only has
to hold eventually for each fixed derivative order. -/
theorem correction_limit
    {F : M → Space} {U : ℕ → M → Space} {ρ : ℕ → ℝ}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hU : ∀ n, ContMDiff planeModel spaceModel ∞ (U n))
    (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop, A.WeightedBound 1 m (ρ n) (U n))
    (houter : ∀ i x, x ∈ tsupport (A.weight i) →
      A.outer i =ᶠ[𝓝 x] (fun _ => 1)) :
    ContMDiff planeModel spaceModel ∞ (manifoldLimitMap F U) ∧
      ∀ p, Tendsto (fun N => mfderiv planeModel spaceModel (manifoldPartialMap F U N) p)
        atTop (𝓝 (mfderiv planeModel spaceModel (manifoldLimitMap F U) p)) := by
  have hpoint (p : M) : ContMDiffAt planeModel spaceModel ∞ (manifoldLimitMap F U) p ∧
      Tendsto (fun N => mfderiv planeModel spaceModel (manifoldPartialMap F U N) p)
        atTop (𝓝 (mfderiv planeModel spaceModel (manifoldLimitMap F U) p)) := by
    obtain ⟨i,hi⟩ := A.exists_weight_ne_zero p
    have hp : p ∈ tsupport (A.weight i) := subset_tsupport _ hi
    have hpS := A.weight_support i hp
    have hpC : p ∈ (coordinateChart (i : M)).source := by
      simpa only [coordinateChart_source,chart_source] using hpS
    have hc := ((coordinateChart_smoothOn (i : M)) p hpC).contMDiffAt
      ((coordinateChart (i : M)).open_source.mem_nhds hpC)
    choose C hC hread using fun m => A.vectorPlaneRead_bound (V := Space) i m
    have hlocal (m : ℕ) : ∀ᶠ n in atTop, ∀ x,
        ‖iteratedFDeriv ℝ m (A.vectorPlaneRead i (U n)) x‖ ≤ C m*ρ n := by
      filter_upwards [hbound m] with n hn x
      have hρn : 0 ≤ ρ n :=
        (norm_nonneg _).trans ((hn i).norm_le (mem_univ (0 : JetPolynomial.Base)))
      have hb := hread m (U n) 1 (ρ n) zero_lt_one le_rfl hρn (hU n) hn
      simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using
        hb m le_rfl x (mem_univ x)
    have heq : ∀ᶠ x in 𝓝 p,
        F x = A.vectorPlaneRead i F (coordinateChart (i : M) x) ∧
        ∀ n, U n x = A.vectorPlaneRead i (U n) (coordinateChart (i : M) x) := by
      filter_upwards [houter i p hp,(chart (i : M)).open_source.mem_nhds hpS] with x ho hx
      exact ⟨A.vectorPlaneRead_coordinateChart_of_outer_one i F hx ho,
        fun n => A.vectorPlaneRead_coordinateChart_of_outer_one i (U n) hx ho⟩
    exact local_coordinate_correction_limit
      (A := fun n => A.vectorPlaneRead i (U n)) (ρ := fun m n => C m*ρ n) p hc
      (A.vectorPlaneRead_smooth i hF) (fun n => A.vectorPlaneRead_smooth i (hU n))
      (fun m => hρ.mul_left (C m)) hlocal heq
  exact ⟨fun p => (hpoint p).1,fun p => (hpoint p).2⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalMetricStep
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact normalized-defect identity for the unsmoothed global map update. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

local instance metricStepFiberNormed_rf8498e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance metricStepFiberSpace_rf8498e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance metricStepDualAdd_rf8498e_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance metricStepDualSmul_rf8498e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricStepSectionNormed
local instance metricStepSectionSpace_rf8498e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma square_smul_normalizedTensorDefect (target : ∀ p : M, CovariantTwoTensor p)
    {δ : ℝ} (hδ : δ ≠ 0) (F : M → Space) :
    δ^2 • normalizedTensorDefect target δ F = target - inducedTensor F := by
  rw [normalizedTensorDefect,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 hδ),one_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasMetricLimit
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized atlas defect controls the actual metric of the limit. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricLimitFiberSpace
local instance metricLimitDualAdd :
    ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricLimitFiberSpace
local instance metricLimitDualSmul_rf8498e_1 :
    ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricLimitFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.metricLimitSectionNormed
local instance metricLimitSectionSpace_rf8498e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
/-- The genuine finite atlas reconstruction carries coordinate convergence
to convergence in each tensor fiber. -/
lemma tensor_tendsto_zero_of_encode
    {H : ℕ → ∀ p : M, CovariantTwoTensor p}
    (hH : ∀ i x, Tendsto (fun n => A.tensorEncode (H n) x i) atTop (𝓝 0))
    (p : M) : Tendsto (fun n => H n p) atTop (𝓝 0) := by
  have hi (i : A.centers) : Tendsto
      (fun n => A.bundleRestore A.tensorTriv i
        (A.bundleLocalize A.tensorTriv i (H n)) p) atTop (𝓝 0) := by
    have h := ((A.tensorTriv i).symmL ℝ p).continuous.tendsto 0 |>.comp
      (hH i (chart (i : M) p))
    simpa only [Function.comp_apply, bundleRestore, tensorEncode, map_zero, smul_zero] using
      h.const_smul (A.outer i p)
  have hs := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  simpa only [A.bundle_sum_restore_localize A.tensorTriv A.tensorTriv_domain,
    Finset.sum_const_zero] using hs

omit [CompactSpace M] in
/-- A bounded normalized defect and a vanishing amplitude imply convergence
of the actual pullback metrics. No convergence of normalized defects is needed. -/
theorem metric_tendsto_of_normalized_coordinates_bound
    {G : ℕ → M → Space} {δ : ℕ → ℝ} {B : ℝ}
    (target : ∀ p : M, CovariantTwoTensor p)
    (hδ : ∀ n, δ n ≠ 0) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ n i x,
      ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i-
        A.tensorEncode target x i‖ ≤ B)
    (p : M) (v w : TangentSpace planeModel p) :
    Tendsto (fun n => inner ℝ (mfderiv planeModel spaceModel (G n) p v)
      (mfderiv planeModel spaceModel (G n) p w)) atTop (𝓝 (target p v w)) := by
  have hlocal (i : A.centers) (x : JetPolynomial.Base) : Tendsto
      (fun n => A.tensorEncode (target-inducedTensor (G n)) x i) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg _)
      (fun n => show ‖A.tensorEncode (target-inducedTensor (G n)) x i‖ ≤
        (δ n)^2*(B+‖A.tensorEncode target x i‖) from ?_)
      (by simpa only [zero_pow (by decide : 2 ≠ 0),zero_mul] using
        (hδ0.pow 2).mul_const (B+‖A.tensorEncode target x i‖))
    have hb := hbound n i x
    have hn : ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i‖ ≤
        B+‖A.tensorEncode target x i‖ := by
      calc
        _ = ‖(A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i-
          A.tensorEncode target x i)+A.tensorEncode target x i‖ := by rw [sub_add_cancel]
        _ ≤ ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i-
          A.tensorEncode target x i‖+‖A.tensorEncode target x i‖ := norm_add_le _ _
        _ ≤ B+‖A.tensorEncode target x i‖ := add_le_add hb le_rfl
    have heq := congrArg (fun T => A.tensorEncode T x i)
      (square_smul_normalizedTensorDefect target (hδ n) (G n))
    rw [A.tensorEncode_smul] at heq
    change (δ n)^2 • A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x i =
      A.tensorEncode (target-inducedTensor (G n)) x i at heq
    rw [← heq,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg (δ n))]
    exact mul_le_mul_of_nonneg_left hn (sq_nonneg (δ n))
  have ht := A.tensor_tendsto_zero_of_encode hlocal p
  have ht' : Tendsto (fun n => (target-inducedTensor (G n)) p : ℕ → TensorFiber)
      atTop (𝓝 0) := ht
  have hv := ((ContinuousLinearMap.apply ℝ (Plane →L[ℝ] ℝ) (show Plane from v)).continuous.tendsto 0).comp ht'
  have hvw := ((ContinuousLinearMap.apply ℝ ℝ (show Plane from w)).continuous.tendsto 0).comp hv
  have hmetric : Tendsto (fun n => target p v w-
      (target-inducedTensor (G n)) p v w) atTop (𝓝 (target p v w-0)) :=
    tendsto_const_nhds.sub hvw
  convert hmetric using 1
  · ext n
    change inner ℝ (mfderiv planeModel spaceModel (G n) p v)
      (mfderiv planeModel spaceModel (G n) p w) =
      target p v w-(target p v w-inducedTensor (G n) p v w)
    rw [sub_sub_cancel]
    rfl
  · simp

omit [CompactSpace M] in
/-- The encoded zeroth-order invariant of the iteration bounds the normalized
metric defect. -/
theorem metric_tendsto_of_encoded_normalized_bound
    {G : ℕ → M → Space} {δ : ℕ → ℝ} {B : ℝ}
    (target : ∀ p : M, CovariantTwoTensor p)
    (hδ : ∀ n, δ n ≠ 0) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hbound : ∀ n x,
      ‖A.tensorEncode (normalizedTensorDefect target (δ n) (G n)) x-
        A.tensorEncode target x‖ ≤ B)
    (p : M) (v w : TangentSpace planeModel p) :
    Tendsto (fun n => inner ℝ (mfderiv planeModel spaceModel (G n) p v)
      (mfderiv planeModel spaceModel (G n) p w)) atTop (𝓝 (target p v w)) := by
  apply A.metric_tendsto_of_normalized_coordinates_bound (B := B) target hδ hδ0 ?_ p v w
  intro n i x
  exact (norm_le_pi_norm _ i).trans (hbound n x)

/-- The stage invariant in encoded tensor coordinates produces the same
isometric limit directly. -/
theorem correction_limit_isometric_of_encoded_bound
    {F : M → Space} {U : ℕ → M → Space} {ρ δ : ℕ → ℝ} {B : ℝ}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (hU : ∀ n, ContMDiff planeModel spaceModel ∞ (U n))
    (hρ : Summable ρ)
    (hbound : ∀ m : ℕ, ∀ᶠ n in atTop, A.WeightedBound 1 m (ρ n) (U n))
    (houter : ∀ i x, x ∈ tsupport (A.weight i) →
      A.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (g : SmoothMetric M) (hδ : ∀ n, δ n ≠ 0) (hδ0 : Tendsto δ atTop (𝓝 0))
    (hdefect : ∀ n x,
      ‖A.tensorEncode (normalizedTensorDefect g.inner (δ n) (manifoldPartialMap F U n)) x-
        A.tensorEncode g.inner x‖ ≤ B) :
    IsSmoothIsometricImmersion M g (manifoldLimitMap F U) := by
  obtain ⟨hs,hd⟩ := A.correction_limit hF hU hρ hbound houter
  refine ⟨hs,?_⟩
  intro p v w
  have hv := ((ContinuousLinearMap.apply ℝ Space (show Plane from v)).continuous.tendsto _).comp (hd p)
  have hw := ((ContinuousLinearMap.apply ℝ Space (show Plane from w)).continuous.tendsto _).comp (hd p)
  exact tendsto_nhds_unique (hv.inner hw)
    (A.metric_tendsto_of_encoded_normalized_bound g.inner hδ hδ0 hdefect p v w)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionScaleControl
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positivity and the cumulative displacement budget for the actual scales. -/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace ClosedSurfaceR4.ExactCorrection

lemma correctionScale_tendsto_zero {t : ℝ} (ht : 0 ≤ t) (hsmall : t ≤ 1/32) :
    Tendsto (correctionScale t) atTop (𝓝 0) :=
  (correctionScale_summable ht hsmall).1.tendsto_atTop_zero

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ExactCorrectionRecurrence
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Scalar estimates for the smooth correction iteration

The scalar recurrence used in `exact-correction.tex`, subsection
"Initialization and passage through the derivative orders", is treated here.
These are estimates for that iteration, not an isometric immersion existence theorem.
-/

namespace ClosedSurfaceR4.ExactCorrection

open Filter
open scoped Topology

/-- A tail of a subsolution is dominated by the corresponding affine recurrence. -/
theorem affine_tail_bound {x : ℕ → ℝ} {a b : ℝ} (ha : 0 ≤ a) (N : ℕ)
    (hstep : ∀ n, N ≤ n → x (n + 1) ≤ a * x n + b) (j : ℕ) :
    x (N + j) ≤ arithGeom a b (x N) j := by
  induction j with
  | zero => simp
  | succ j hj =>
    calc
      x (N + (j + 1)) ≤ a * x (N + j) + b := hstep (N + j) (by omega)
      _ ≤ a * arithGeom a b (x N) j + b := by gcongr
      _ = arithGeom a b (x N) (j + 1) := rfl

/-- An affine subsolution with contraction coefficient eventually lies below any
strict upper bound for the fixed point. -/
theorem eventually_lt_of_affine_tail {x : ℕ → ℝ} {a b L : ℝ}
    (ha : 0 ≤ a) (ha1 : a < 1) (hL : b / (1 - a) < L) (N : ℕ)
    (hstep : ∀ n, N ≤ n → x (n + 1) ≤ a * x n + b) :
    ∀ᶠ n in atTop, x n < L := by
  have ht : Tendsto (arithGeom a b (x N)) atTop (𝓝 (b / (1 - a))) :=
    tendsto_arithGeom_nhds_of_lt_one ha ha1
  obtain ⟨K, hK⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hL))
  filter_upwards [eventually_ge_atTop (N + K)] with n hn
  have hNK : N + (n - N) = n := by omega
  have hbound := affine_tail_bound ha N hstep (n - N)
  rw [hNK] at hbound
  exact lt_of_le_of_lt hbound (hK (n - N) (by omega))

end ClosedSurfaceR4.ExactCorrection

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_FixedOrderThreshold
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! At each fixed order, all analytic smallness conditions and the
finite derivative budget hold below one positive scale threshold. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace ClosedSurfaceR4.ExactCorrection

lemma positive_power_threshold (c p b : ℝ) (hp : 0 < p) (hb : 0 < b) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < ε → c*t^p < b := by
  have hf : ContinuousAt (fun t : ℝ => c*t^p) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const 0 p (Or.inr hp.le))
  have he : ∀ᶠ t in 𝓝 (0 : ℝ), c*t^p < b :=
    hf.eventually (gt_mem_nhds (by simpa only [Real.zero_rpow hp.ne',mul_zero] using hb))
  obtain ⟨ε,hε,heε⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨min ε 1,lt_min hε zero_lt_one,min_le_right _ _,?_⟩
  intro t ht hsmall
  apply heε
  simpa only [Real.dist_eq,sub_zero,abs_of_pos ht] using hsmall.trans_le (min_le_left ε 1)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CorrectionBudgetThresholds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Simultaneous preservation of the finite input and normalized metric budgets. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

theorem correction_budget_threshold {A B a N L : ℝ} (hAB : A < B) (ha : 0 < a) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ t : ℝ, 0 < t → t < ε →
      A+N*t^(1/5 : ℝ)*(1+B) ≤ B ∧ L*(1+2*B)*t^(1/5 : ℝ) ≤ a/8 := by
  obtain ⟨ε₁,hε₁,hε₁1,h₁⟩ := positive_power_threshold (N*(1+B)) (1/5) (B-A)
    (by norm_num) (sub_pos.mpr hAB)
  obtain ⟨ε₂,hε₂,_,h₂⟩ := positive_power_threshold (L*(1+2*B)) (1/5) (a/8)
    (by norm_num) (by positivity)
  refine ⟨min ε₁ ε₂,lt_min hε₁ hε₂,(min_le_left _ _).trans hε₁1,?_⟩
  intro t ht htε
  have hb := (h₁ t ht (htε.trans_le (min_le_left _ _))).le
  have hm := (h₂ t ht (htε.trans_le (min_le_right _ _))).le
  exact ⟨by nlinarith,hm⟩

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InputSize
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite joint input norms for the adaptive correction iteration. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputSizeFiberNormed
local instance inputSizeSectionNormed_rf8498e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance inputSizeSectionSpace_rf8498e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma inputSize_le {t C : ℝ} {m : ℕ} {G : M → Space}
    {H : ∀ p : M, CovariantTwoTensor p}
    (hC : 0 ≤ C) (hb : A.InputBound t m C G H) :
    A.inputSize t m G H ≤ C := by
  exact csInf_le ⟨0,fun _ h => h.1⟩ ⟨hC,hb⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveOrderControl
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar progress of an adaptive derivative order. No uniform control of
all the higher input norms is required. -/
noncomputable section
open Filter
open scoped Topology
namespace ClosedSurfaceR4.ExactCorrection

lemma eventually_lt_of_eventual_vanishing_recurrence
    {x c : ℕ → ℝ} {A L : ℝ} (hx : ∀ n, 0 ≤ x n) (hA : 0 ≤ A)
    (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ᶠ n in atTop, x (n+1) ≤ A+c n*(1+x n)) (hAL : A < L) :
    ∀ᶠ n in atTop, x n < L := by
  let a : ℝ := (L-A)/(2*(L+1))
  have hL : 0 < L := lt_of_le_of_lt hA hAL
  have hden : 0 < 2*(L+1) := by positivity
  have ha : 0 < a := div_pos (sub_pos.mpr hAL) hden
  have ha1 : a < 1 := by
    dsimp [a]
    apply (div_lt_one hden).mpr
    linarith
  have hafix : (A+a)/(1-a) < L := by
    apply (div_lt_iff₀ (sub_pos.mpr ha1)).mpr
    have heq : a*(L+1) = (L-A)/2 := by dsimp [a]; field_simp
    nlinarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hstep.and (hc.eventually (gt_mem_nhds ha)))
  apply eventually_lt_of_affine_tail ha.le ha1 hafix N
  intro n hn
  have h1 := (hN n hn).1
  have h2 := mul_le_mul_of_nonneg_right (hN n hn).2.le (by linarith [hx n] : 0 ≤ 1+x n)
  nlinarith

lemma order_tendsto_of_no_constant_tail {k : ℕ → ℕ} (hmono : Monotone k)
    (hno : ∀ j N, ¬ ∀ n ≥ N, k n = j) : Tendsto k atTop atTop := by
  apply hmono.tendsto_atTop_atTop_iff.mpr
  intro m
  induction m with
  | zero => exact ⟨0,Nat.zero_le _⟩
  | succ m ih =>
    obtain ⟨N,hN⟩ := ih
    by_contra h
    push Not at h
    apply hno m N
    intro n hn
    have hupper := h n
    have hlower := hN.trans (hmono hn)
    omega

/-- Holding one order forever is impossible: every fixed higher input norm
contracts toward the baseline, so the rule must eventually advance. -/
theorem adaptive_order_tendsto
    {k : ℕ → ℕ} {x : ℕ → ℕ → ℝ} {t : ℕ → ℝ}
    {A B : ℝ} {N : ℕ → ℕ → ℝ} {ε : ℕ → ℝ} {r : ℕ → ℕ}
    (hA : 0 ≤ A) (hAB : A < B) (_hB : 0 < B)
    (hN : ∀ j m, 0 ≤ N j m) (hε : ∀ j, 0 < ε j)
    (ht : ∀ n, 0 < t n) (ht0 : Tendsto t atTop (𝓝 0))
    (hx : ∀ m n, 0 ≤ x m n)
    (hstep : ∀ m n, x m (n+1) ≤ A+N (k n) m*(t n)^(1/5 : ℝ)*(1+x m n))
    (hmono : Monotone k)
    (hadvance : ∀ n, t n < ε (k n+1) →
      A+N (k n) (r (k n+1))*(t n)^(1/5 : ℝ)*(1+x (r (k n+1)) n) ≤ B →
      k (n+1) = k n+1) : Tendsto k atTop atTop := by
  apply order_tendsto_of_no_constant_tail hmono
  intro j K hconstant
  have hpow : Tendsto (fun n => (t n)^(1/5 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (1/5 : ℝ) ≠ 0)] using
      ht0.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 1/5))
  have hc : Tendsto (fun n => N j (r (j+1))*(t n)^(1/5 : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpow.const_mul (N j (r (j+1)))
  have hrec : ∀ᶠ n in atTop,
      x (r (j+1)) (n+1) ≤ A+N j (r (j+1))*(t n)^(1/5 : ℝ)*(1+x (r (j+1)) n) := by
    filter_upwards [eventually_ge_atTop K] with n hn
    simpa only [hconstant n hn] using hstep (r (j+1)) n
  have hxB := eventually_lt_of_eventual_vanishing_recurrence (hx (r (j+1))) hA hc hrec hAB
  obtain ⟨η,hη,_,hηbound⟩ := correction_budget_threshold
    (N := N j (r (j+1))) (L := (0 : ℝ)) hAB (by norm_num : (0 : ℝ) < 1)
  have hsmall := ht0.eventually (gt_mem_nhds (lt_min (hε (j+1)) hη))
  obtain ⟨n,hnK,hnB,hnt⟩ := (eventually_ge_atTop K |>.and (hxB.and hsmall)).exists
  have hkn := hconstant n hnK
  have hknext := hconstant (n+1) (by omega)
  have hb := (hηbound (t n) (ht n) (hnt.trans_le (min_le_right _ _))).1
  have hxle : x (r (j+1)) n ≤ B := hnB.le
  have hmul : N j (r (j+1))*(t n)^(1/5 : ℝ)*(1+x (r (j+1)) n) ≤
      N j (r (j+1))*(t n)^(1/5 : ℝ)*(1+B) :=
    mul_le_mul_of_nonneg_left (add_le_add le_rfl hxle)
      (mul_nonneg (hN j (r (j+1))) (Real.rpow_nonneg (ht n).le _))
  have hadv := hadvance n (by rw [hkn]; exact hnt.trans_le (min_le_left _ _))
    (by rw [hkn]; linarith)
  omega

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveCorrectionSequence
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construction of the correction sequence, and unbounded growth of the
finite derivative order despite the absence of uniform high-order input bounds. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection WeightedEstimates
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions_1
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance sequenceFiberNormed_rf8498e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance sequenceFiberSpace_rf8498e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance sequenceDualAdd_rf8498e_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance sequenceDualSmul_rf8498e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.instDecidable_solutions_1
local instance sequenceFiberNormed_rf8498e_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance sequenceFiberSpace_rf8498e_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance sequenceDualAdd_rf8498e_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance sequenceDualSmul_rf8498e_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (c : PreparedCorrection d) (hF : ContMDiff planeModel spaceModel ∞ F)
  {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)

local instance sequenceSectionNormed_rf8498e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance sequenceSectionSpace_rf8498e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma sequence_succ_map (seed : c.Stage t 0) (n : ℕ) :
    (c.sequence hF ht htsmall seed (n+1)).map =
    (c.sequence hF ht htsmall seed n).map+c.increment hF ht htsmall seed n :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).map_eq

lemma sequence_succ_order (seed : c.Stage t 0) (n : ℕ) :
    (c.sequence hF ht htsmall seed (n+1)).order =
      if (c.sequence hF ht htsmall seed n).CanAdvance then
        (c.sequence hF ht htsmall seed n).order+1 else
        (c.sequence hF ht htsmall seed n).order :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).order_eq

lemma sequence_order_monotone (seed : c.Stage t 0) :
    Monotone (fun n => (c.sequence hF ht htsmall seed n).order) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [c.sequence_succ_order hF ht htsmall seed n]
  split_ifs <;> omega

lemma increment_smooth (seed : c.Stage t 0) (n : ℕ) :
    ContMDiff planeModel spaceModel ∞ (c.increment hF ht htsmall seed n) :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).smooth

lemma sequence_partialMap (seed : c.Stage t 0) (n : ℕ) :
    (c.sequence hF ht htsmall seed n).map =
    manifoldPartialMap seed.map (c.increment hF ht htsmall seed) n := by
  induction n with
  | zero => funext x; simp [sequence,manifoldPartialMap]
  | succ n ih =>
    rw [c.sequence_succ_map hF ht htsmall seed n,ih]
    funext x
    simp only [Pi.add_apply,manifoldPartialMap,Finset.sum_range_succ]
    abel

lemma sequence_size_recurrence (seed : c.Stage t 0) (m n : ℕ) :
    (c.sequence hF ht htsmall seed (n+1)).size m ≤ c.baseline+
      c.N (c.sequence hF ht htsmall seed n).order m*(correctionScale t n)^(1/5 : ℝ)*
        (1+(c.sequence hF ht htsmall seed n).size m) := by
  let s := c.sequence hF ht htsmall seed n
  have hex := s.finiteInput ht htsmall m
  have hx : 0 ≤ s.size m := d.A.inputSize_nonneg hex
  have hbound := (c.chosenTransition hF ht htsmall s).recurrence m (s.size m)
    hx (d.A.inputSize_bound hex)
  exact d.A.inputSize_le (add_nonneg c.baseline_nonneg
    (mul_nonneg (mul_nonneg (c.N_nonneg s.order m)
      (Real.rpow_nonneg (correctionScale_pos ht n).le _)) (by linarith))) hbound

/-- The adaptive order really tends to infinity. The proof uses the actual
finite norm of every stage and the all-order affine recurrence. -/
theorem sequence_order_tendsto (seed : c.Stage t 0) :
    Tendsto (fun n => (c.sequence hF ht htsmall seed n).order) atTop atTop := by
  apply adaptive_order_tendsto (x := fun m n => (c.sequence hF ht htsmall seed n).size m)
    (t := correctionScale t) (N := c.N) (ε := c.ε) (r := correctionInputOrder)
    c.baseline_nonneg (lt_trans c.baseline_lt (by linarith [c.budget_pos])) c.budget_pos
    c.N_nonneg c.ε_pos (correctionScale_pos ht)
    (correctionScale_tendsto_zero ht.le htsmall)
  · intro m n
    exact d.A.inputSize_nonneg ((c.sequence hF ht htsmall seed n).finiteInput ht htsmall m)
  · exact c.sequence_size_recurrence hF ht htsmall seed
  · exact c.sequence_order_monotone hF ht htsmall seed
  · intro n hε hb
    have ha : (c.sequence hF ht htsmall seed n).CanAdvance := ⟨hε,hb⟩
    rw [c.sequence_succ_order hF ht htsmall seed n,ite_eq_left ha]

lemma increment_eventual_bound (seed : c.Stage t 0) (m : ℕ) :
    ∀ᶠ n in atTop, d.A.WeightedBound 1 m (c.ρ*correctionScale t n)
      (c.increment hF ht htsmall seed n) := by
  filter_upwards [(c.sequence_order_tendsto hF ht htsmall seed).eventually
    (eventually_ge_atTop (2*m))] with n hn
  exact (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).small m
    (by unfold correctionOrder; omega)

lemma sequence_amplitude_tendsto (seed : c.Stage t 0) :
    Tendsto (fun n => (correctionScale t n)^
      (correctionOrder (c.sequence hF ht htsmall seed n).order : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => Real.rpow_nonneg (correctionScale_pos ht n).le _)
    (fun n => ?_) (correctionScale_tendsto_zero ht.le htsmall)
  have hsn := correctionScale_pos ht n
  have hs1 : correctionScale t n ≤ 1 :=
    (correctionScale_le_initial ht.le htsmall n).trans (by linarith)
  have hexp : (1 : ℝ) ≤ (correctionOrder (c.sequence hF ht htsmall seed n).order : ℝ) := by
    unfold correctionOrder
    exact_mod_cast (show 1 ≤ (c.sequence hF ht htsmall seed n).order+10 by omega)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hsn hs1 hexp

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveExactCorrection
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The adaptive construction produces a smooth isometric immersion
from admissible finite initial data by choosing a correction sequence. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance exactFiberNormed_rf8498e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance exactFiberSpace_rf8498e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance exactDualAdd_rf8498e_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance exactDualSmul_rf8498e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection

local instance exactFiberNormed_rf8498e_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance exactFiberSpace_rf8498e_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance exactDualAdd_rf8498e_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance exactDualSmul_rf8498e_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance exactSectionNormed_rf8498e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance exactSectionSpace_rf8498e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Construction, growth of derivative order, and passage to the actual
metric limit are combined here. Only finite initial input data remain. -/
theorem sequence_limit_isometric (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F) {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)
    (seed : c.Stage t 0) : IsSmoothIsometricImmersion M g
      (manifoldLimitMap seed.map (c.increment hF ht htsmall seed)) := by
  let U := c.increment hF ht htsmall seed
  let δ := fun n => (correctionScale t n)^
    (correctionOrder (c.sequence hF ht htsmall seed n).order : ℝ)
  change IsSmoothIsometricImmersion M g (manifoldLimitMap seed.map U)
  apply d.A.correction_limit_isometric_of_encoded_bound seed.smooth
    (c.increment_smooth hF ht htsmall seed)
    ((correctionScale_summable ht.le htsmall).1.mul_left c.ρ)
    (c.increment_eventual_bound hF ht htsmall seed) d.outer_locally_one g
    (δ := δ) (B := c.a/8)
  · intro n
    exact ne_of_gt (Real.rpow_pos_of_pos (correctionScale_pos ht n) _)
  · exact c.sequence_amplitude_tendsto hF ht htsmall seed
  · intro n x
    have hh := (c.sequence hF ht htsmall seed n).metric x
    rw [c.sequence_partialMap hF ht htsmall seed n] at hh
    exact hh


end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasCorrectionBudget
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual correction series retains its finite atlas displacement budget. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection WeightedEstimates

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma localize_tsum (p : M) (χ : M → ℝ) (U : ℕ → M → Space) :
    localize p χ (fun x => ∑' n, U n x) = fun x => ∑' n, localize p χ (U n) x := by
  funext x
  by_cases hx : x ∈ (chart p).target
  · simp only [localize,indicator_of_mem hx]
    exact (tsum_const_smul'' _).symm
  · simp only [localize,indicator_of_notMem hx,tsum_zero]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

/-- Bounds at a fixed finite order pass to the actual sum with the sum of
the bounds, rather than a larger coordinate-transition constant. -/
theorem weightedBound_tsum {U : ℕ → M → Space} {ρ : ℕ → ℝ} {m : ℕ}
    (hU : ∀ n, ContMDiff planeModel spaceModel ∞ (U n)) (hρ : Summable ρ)
    (hbound : ∀ n, A.WeightedBound 1 m (ρ n) (U n)) :
    A.WeightedBound 1 m (∑' n, ρ n) (fun x => ∑' n, U n x) := by
  intro i
  rw [localize_tsum]
  have hs (n : ℕ) : ContDiff ℝ ∞ (localize (i : M) (A.weight i) (U n)) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) (hU n)
  have hb (j : ℕ) (hj : j ≤ m) (n : ℕ) (x : JetPolynomial.Base) :
      ‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) (U n)) x‖ ≤ ρ n := by
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using
      hbound n i j hj x (mem_univ x)
  intro j hj x _
  simp only [one_pow,one_mul,iteratedFDerivWithin_univ]
  rw [iteratedFDeriv_tsum_apply (N := (m : ℕ∞))
    (v := fun _ => ρ) (fun n => (hs n).of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (fun _ _ => hρ) (fun k n y hk => hb k (by exact_mod_cast hk) n y)
    (by exact_mod_cast hj) x]
  exact tsum_of_norm_bounded hρ.hasSum (fun n => hb j hj n x)

end SmoothingAtlas

namespace PreparedCorrection
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
variable (c : PreparedCorrection d) (hF : ContMDiff planeModel spaceModel ∞ F)
  {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)

/-- Every constructed increment has the zeroth, first, and second derivative
budget, including the stages before the order has increased. -/
lemma increment_c2_bound (seed : c.Stage t 0) (n : ℕ) :
    d.A.WeightedBound 1 2 (c.ρ*correctionScale t n)
      (c.increment hF ht htsmall seed n) :=
  (c.chosenTransition hF ht htsmall (c.sequence hF ht htsmall seed n)).small 2
    (by unfold correctionOrder; omega)

/-- The limit remains within the total C² displacement budget of its seed. -/
theorem limit_seed_displacement_bound (seed : c.Stage t 0) :
    d.A.WeightedBound 1 2 (2*c.ρ*t)
      (manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-seed.map) := by
  have hsum := (correctionScale_summable ht.le htsmall).1.mul_left c.ρ
  have hb := d.A.weightedBound_tsum (c.increment_smooth hF ht htsmall seed)
    hsum (c.increment_c2_bound hF ht htsmall seed)
  have he : manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-seed.map =
      (fun x => ∑' n, c.increment hF ht htsmall seed n x) := by
    funext x
    simp only [Pi.sub_apply,manifoldLimitMap,add_sub_cancel_left]
  rw [he]
  intro i
  apply (hb i).mono_const
  rw [tsum_mul_left]
  calc
    c.ρ*(∑' n, correctionScale t n) ≤ c.ρ*(2*t) :=
      mul_le_mul_of_nonneg_left (correctionScale_tsum_le ht.le htsmall) c.ρ_pos.le
    _ = 2*c.ρ*t := by ring

/-- The initial margin and the convergent correction budget preserve the
same fixed C² neighborhood used to construct the entire sequence. -/
theorem limit_reference_displacement_bound (seed : c.Stage t 0) :
    d.A.WeightedBound 1 2 (c.ρ/4)
      (manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-F) := by
  have hsum := (correctionScale_summable ht.le htsmall).1.mul_left c.ρ
  have hs := (d.A.correction_limit seed.smooth (c.increment_smooth hF ht htsmall seed)
    hsum (c.increment_eventual_bound hF ht htsmall seed) d.outer_locally_one).1
  have hseed : d.A.WeightedBound 1 2 (c.ρ/8) (seed.map-F) := by
    simpa only [stageRadius,Finset.range_zero,Finset.sum_empty,mul_zero,add_zero] using seed.near
  have hb := d.A.weightedBound_add (seed.smooth.sub hF) (hs.sub seed.smooth)
    zero_le_one hseed (c.limit_seed_displacement_bound hF ht htsmall seed)
  have he : manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-F =
      (seed.map-F)+(manifoldLimitMap seed.map (c.increment hF ht htsmall seed)-seed.map) := by
    abel
  rw [he]
  intro i
  apply (hb i).mono_const
  have hρ := c.ρ_pos.le
  nlinarith [mul_le_mul_of_nonneg_left htsmall c.ρ_pos.le]

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AdaptiveExactControl
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed exact correction retains the C² geometry budget. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open ExactCorrection
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection

/-- The same, concretely constructed limit is isometric and close in C² to
both the initial stage and the fixed reference immersion. -/
theorem exact_correction_with_control (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F) {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32)
    (seed : c.Stage t 0) :
    ∃ G : M → Space, IsSmoothIsometricImmersion M g G ∧
      d.A.WeightedBound 1 2 (2*c.ρ*t) (G-seed.map) ∧
      d.A.WeightedBound 1 2 (c.ρ/4) (G-F) := by
  exact ⟨_,c.sequence_limit_isometric hF ht htsmall seed,
    c.limit_seed_displacement_bound hF ht htsmall seed,
    c.limit_reference_displacement_bound hF ht htsmall seed⟩

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledInitialMap
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial contraction of an approximate immersion. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualSmul
lemma initial_contraction_displacement {δ : ℝ} (hδ1 : δ^2 ≤ 1) :
    |Real.sqrt (1-δ^2)-1| ≤ δ^2 := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr hδ1)
  have hn := Real.sqrt_nonneg (1-δ^2)
  have hu : Real.sqrt (1-δ^2) ≤ 1 := by nlinarith [sq_nonneg δ]
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  nlinarith

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

namespace SmoothingAtlas
local instance initialBoundFiberNormed_rf8498e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_rf8498e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd_rf8498e_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_rf8498e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance initialBoundSectionNormed_rf8498e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_rf8498e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma weightedBound_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C : ℝ} {m : ℕ}
    (hb : A.WeightedBound s m C F) (a : ℝ) :
    A.WeightedBound s m (|a| * C) (a • F) := by
  intro i
  rw [localize_smul]
  exact (hb i).const_smul uniqueDiffOn_univ
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn a

omit [CompactSpace M] in
lemma shifted_zero_to_weighted {F : M → Space} {P : ℝ} {q : ℕ}
    (hb : A.ShiftedBound q 0 1 P F) : A.WeightedBound 1 q P F := by
  intro i j hj x _
  have hh := hb i j (by omega) x
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_InitialCorrectionStage
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Build the first actual correction stage from finite metric accuracy. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialStageFiberNormed
local instance initialStageFiberSpace_rf8498e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialStageDualAdd_rf8498e_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialStageDualSmul_rf8498e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection


attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialStageFiberNormed
local instance initialStageFiberSpace_rf8498e_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialStageDualAdd_rf8498e_2 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialStageDualSmul_rf8498e_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialStageSectionNormed_rf8498e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialStageSectionSpace_rf8498e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The actual exact correction tends to the original map in C² as the
initial smoothing scale tends to zero. This retains the size of the initial
contraction instead of replacing it by the fixed geometric radius. -/
theorem exact_correction_initial_displacement_oai (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F) {t P : ℝ}
    (ht : 0 < t) (htsmall : t ≤ 1/32) (hP : 0 ≤ P)
    (hmap : d.A.ShiftedBound 2 0 1 P F)
    (seed : c.Stage t 0)
    (hseed : seed.map = Real.sqrt (1-(t^(10 : ℝ))^2) • F) :
    ∃ G : M → Space, IsSmoothIsometricImmersion M g G ∧
      d.A.WeightedBound 1 2 ((t^(10 : ℝ))^2*P+2*c.ρ*t) (G-F) := by
  have ht1 : t ≤ 1 := by linarith
  have hδle : t^(10 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hδsq : (t^(10 : ℝ))^2 ≤ 1 :=
    pow_le_one₀ (Real.rpow_nonneg ht.le _) hδle
  have hbase := d.A.shifted_zero_to_weighted hmap
  have hh := d.A.weightedBound_const_smul hF hbase (Real.sqrt (1-(t^(10 : ℝ))^2)-1)
  have hsf : d.A.WeightedBound 1 2 ((t^(10 : ℝ))^2*P) (seed.map-F) := by
    have hid : seed.map-F = (Real.sqrt (1-(t^(10 : ℝ))^2)-1) • F := by
      rw [hseed,sub_smul,one_smul]
    rw [hid]
    intro i
    exact (hh i).mono_const
      (mul_le_mul_of_nonneg_right (initial_contraction_displacement hδsq) hP)
  obtain ⟨G,hG,hGs,_⟩ := c.exact_correction_with_control hF ht htsmall seed
  refine ⟨G,hG,?_⟩
  have hb := d.A.weightedBound_add (seed.smooth.sub hF) (hG.1.sub seed.smooth)
    zero_le_one hsf hGs
  have hid : G-F = (seed.map-F)+(G-seed.map) := by abel
  rw [hid]
  exact hb

end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.PreparedCorrection.exact_correction_initial_displacement_oai.{u_1}
