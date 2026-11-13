-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_metric_with_property
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:34:54.527508+00:00
-- url     : https://prove2.me/submissions/02c68648-4f5c-40d3-b41d-537e6d4457ec

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
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
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_PreparedCorrection_exact_correction_initial_displacement
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_anchored_prepared_correction

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



lemma WeightedBound.mono_order {U : Set E} {s C : ℝ} {m r : ℕ} {f : E → F}
    (h : WeightedBound U s m C f) (hr : r ≤ m) : WeightedBound U s r C f :=
  fun j hj => h j (hj.trans hr)


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
local instance metricBoundSectionNormed_r097d1e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance metricBoundSectionSpace_r097d1e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
local instance quadraticAtlasSectionSpace_r097d1e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_ShiftedSmoothingBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothing bounds with an unweighted finite derivative prefix. In the
correction scheme the map has prefix order two and the metric defect order zero. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates MeasureTheory
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma ShiftedBound.deriv_le {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) {j : ℕ} (hj : j ≤ q + m) (x : Base) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ C / s ^ (j - q) := by
  apply (le_div_iff₀ (pow_pos hs _)).mpr
  simpa only [mul_comm] using h j hj x

end ClosedSurfaceR4.FiniteOrderSmoothing

end

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PositivePolynomialBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit normal-frame budgets have fixed polynomial growth. This
keeps their exponents independent of multiplicative input constants. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

lemma polynomialBound_id : HasPolynomialBound (fun x => x) := by
  exact ⟨1,1,le_rfl,fun x hx => ⟨zero_le_one.trans hx,by simp⟩⟩

lemma HasPolynomialBound.pow {f : ℝ → ℝ} (hf : HasPolynomialBound f) (n : ℕ) :
    HasPolynomialBound (fun x => (f x)^n) := by
  obtain ⟨d,C,hC,hf⟩ := hf
  refine ⟨d*n,C^n,one_le_pow₀ hC,?_⟩
  intro x hx
  have hh := hf x hx
  refine ⟨pow_nonneg hh.1 _,?_⟩
  calc
    (f x)^n ≤ (C*x^d)^n := pow_le_pow_left₀ hh.1 hh.2 _
    _ = C^n*x^(d*n) := by rw [mul_pow,pow_mul]

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialBudgetAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition and inverse-scale evaluation of the polynomial
budgets in the correction construction. -/
noncomputable section
namespace ClosedSurfaceR4.RealModes

/-- Polynomial degree is chosen before all multiplicative constants. -/
theorem HasPolynomialBound.at_inverse_scale {f : ℝ → ℝ} (hf : HasPolynomialBound f)
    (p : ℕ) : ∃ d : ℕ, ∀ D : ℝ, 1 ≤ D → ∃ C : ℝ, 1 ≤ C ∧
      ∀ z : ℝ, 0 < z → z ≤ 1 → 0 ≤ f (D/z^p) ∧ f (D/z^p) ≤ C/z^d := by
  obtain ⟨d,A,hA,hf⟩ := hf
  refine ⟨p*d,fun D hD => ⟨A*D^d,one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hD),?_⟩⟩
  intro z hz hz1
  have hzD : 1 ≤ D/z^p := by
    apply (le_div_iff₀ (pow_pos hz p)).mpr
    simpa only [one_mul] using (pow_le_one₀ hz.le hz1).trans hD
  refine ⟨(hf _ hzD).1,?_⟩
  calc
    f (D/z^p) ≤ A*(D/z^p)^d := (hf _ hzD).2
    _ = (A*D^d)/z^(p*d) := by rw [div_pow,pow_mul]; ring

end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShiftedScaleGain
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inherited derivatives gain a scale ratio above the fixed prefix. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Reducing the scale preserves the unweighted prefix and contracts all
higher weighted derivatives by at least `τ/t`. -/
theorem ShiftedBound.shrink_with_prefix {q m : ℕ} {t τ A C : ℝ} {f : Base → V}
    (hb : ShiftedBound q 0 t A f) (hc : ShiftedBound q m t C f)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hA : 0 ≤ A) (hC : 0 ≤ C) :
    ShiftedBound q m τ (A + (τ / t) * C) f := by
  intro j hj x
  by_cases hjq : j ≤ q
  · have h := hb j (by omega) x
    simp only [Nat.sub_eq_zero_of_le hjq, pow_zero, one_mul] at h ⊢
    exact h.trans (le_add_of_nonneg_right (mul_nonneg (div_nonneg hτ ht.le) hC))
  · have hp : (τ / t) ^ (j - q) ≤ τ / t := by
      simpa only [pow_one] using pow_le_pow_of_le_one (div_nonneg hτ ht.le)
        ((div_le_one ht).mpr hτt) (show 1 ≤ j - q by omega)
    calc
      _ ≤ τ ^ (j - q) * (C / t ^ (j - q)) :=
        mul_le_mul_of_nonneg_left (hc.deriv_le ht hj x) (pow_nonneg hτ _)
      _ = (τ / t) ^ (j - q) * C := by rw [div_pow]; ring
      _ ≤ (τ / t) * C := mul_le_mul_of_nonneg_right hp hC
      _ ≤ _ := le_add_of_nonneg_left hA

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalScaleGain
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inherited-map part of the all-order correction recurrence. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
/-- Shrinking the scale gains one ratio in every positive weighted order. -/
theorem shifted_shrink_with_prefix {q m : ℕ} {t τ P C : ℝ} {f : M → V}
    (hb : A.ShiftedBound q 0 t P f) (hc : A.ShiftedBound q m t C f)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    A.ShiftedBound q m τ (P + (τ / t) * C) f :=
  fun i => (hb i).shrink_with_prefix (hc i) ht hτ hτt hP hC

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalInputRecurrence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Both components of the actual next input admit a common recurrence bound. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates JetPolynomial
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma weighted_shrink_with_norm {E W : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : E → W} {s P C : ℝ} {m : ℕ} (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hp : WeightedEstimates.WeightedBound univ 1 0 P f)
    (hc : WeightedEstimates.WeightedBound univ 1 m C f) :
    WeightedEstimates.WeightedBound univ s m (P+s*C) f := by
  intro j hj x hx
  by_cases hz : j = 0
  · subst j
    have h := hp 0 le_rfl x hx
    simp only [pow_zero,one_mul] at h ⊢
    exact h.trans (le_add_of_nonneg_right (mul_nonneg hs hC))
  · have h := hc j hj x hx
    simp only [one_pow,one_mul] at h
    calc
      _ ≤ s^j*C := mul_le_mul_of_nonneg_left h (pow_nonneg hs _)
      _ ≤ s*C := mul_le_mul_of_nonneg_right
        (by simpa only [pow_one] using pow_le_pow_of_le_one hs hs1 (show 1 ≤ j by omega)) hC
      _ ≤ P+s*C := le_add_of_nonneg_left (by
        exact le_trans (norm_nonneg (f x)) (hp.norm_le (mem_univ x)))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputRecurrenceFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputRecurrenceFiberSpace
omit [CompactSpace M] in
lemma tensor_shrink_with_norm {T : ∀ p : M, CovariantTwoTensor p} {s P C : ℝ} {m : ℕ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hp : A.TensorWeightedBound 1 0 P T) (hc : A.TensorWeightedBound 1 m C T) :
    A.TensorWeightedBound s m (P+s*C) T :=
  fun i => weighted_shrink_with_norm hs hs1 hC (hp i) (hc i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScaledInitialMap
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
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

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualSmul
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberNormed
local instance initialSectionNormed_r097d1e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialSectionSpace_r097d1e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma inducedTensor_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    inducedTensor (a • F) = a^2 • inducedTensor F := by
  funext p
  ext v w
  have hd : (mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) =
      a • (mfderiv planeModel spaceModel F p : Plane →L[ℝ] Space) :=
    const_smul_mfderiv ((hF p).mdifferentiableAt (by simp)) a
  change inner ℝ ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) v)
    ((mfderiv planeModel spaceModel (a • F) p : Plane →L[ℝ] Space) w) =
    a^2*inner ℝ (mfderiv planeModel spaceModel F p v) (mfderiv planeModel spaceModel F p w)
  have hv := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from v)) hd
  have hw := congrArg (fun L : Plane →L[ℝ] Space => L (show Plane from w)) hd
  change (mfderiv planeModel spaceModel (a • F) p v : Space) =
    a • (mfderiv planeModel spaceModel F p v : Space) at hv
  change (mfderiv planeModel spaceModel (a • F) p w : Space) =
    a • (mfderiv planeModel spaceModel F p w : Space) at hw
  calc
    _ = inner ℝ (a • (mfderiv planeModel spaceModel F p v : Space))
        (a • (mfderiv planeModel spaceModel F p w : Space)) :=
      congrArg₂ (fun x y : Space => inner ℝ x y) hv hw
    _ = _ := by rw [real_inner_smul_left,real_inner_smul_right]; ring

/-- The normalized defect after the initial scalar contraction has exactly
the reference metric plus a scaled copy of the old metric error. -/
theorem normalizedTensorDefect_initial {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (target : ∀ p : M, CovariantTwoTensor p) {δ : ℝ} (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) :
    normalizedTensorDefect target δ (Real.sqrt (1-δ^2) • F) =
      target+(1-(δ^2)⁻¹) • (inducedTensor F-target) := by
  rw [normalizedTensorDefect,inducedTensor_const_smul hF,Real.sq_sqrt (sub_nonneg.mpr hδ1)]
  funext p
  ext v w
  change (δ^2)⁻¹*(target p v w-(1-δ^2)*inducedTensor F p v w) =
    target p v w+(1-(δ^2)⁻¹)*(inducedTensor F p v w-target p v w)
  field_simp
  ring

lemma initial_contraction_displacement {δ : ℝ} (hδ1 : δ^2 ≤ 1) :
    |Real.sqrt (1-δ^2)-1| ≤ δ^2 := by
  have hsq := Real.sq_sqrt (sub_nonneg.mpr hδ1)
  have hn := Real.sqrt_nonneg (1-δ^2)
  have hu : Real.sqrt (1-δ^2) ≤ 1 := by nlinarith [sq_nonneg δ]
  rw [abs_of_nonpos (sub_nonpos.mpr hu)]
  nlinarith

lemma initial_normalized_coefficient_bound {δ C : ℝ} (hδ : δ ≠ 0)
    (hδ1 : δ^2 ≤ 1) (hC : 0 ≤ C) :
    |1-(δ^2)⁻¹| * (δ^2*C) ≤ C := by
  have hinv : 1 ≤ (δ^2)⁻¹ := (one_le_inv₀ (sq_pos_of_ne_zero hδ)).mpr hδ1
  rw [abs_of_nonpos (sub_nonpos.mpr hinv)]
  have he : -(1-(δ^2)⁻¹)*(δ^2*C) = (1-δ^2)*C := by
    field_simp
    ring
  rw [he]
  nlinarith [sq_nonneg δ]

variable [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialDualSmul
local instance initialSectionNormed_r097d1e_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialSectionSpace_r097d1e_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Finite metric accuracy before contraction becomes the normalized
accuracy required to start the correction iteration. -/
theorem normalized_initial_error_bound (A : SmoothingAtlas M)
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    {target : ∀ p : M, CovariantTwoTensor p}
    (htarget : ContMDiff planeModel (planeModel.prod 𝓘(ℝ, TensorFiber)) ∞
      (fun p => TotalSpace.mk' TensorFiber p (target p)))
    {δ C s : ℝ} {m : ℕ} (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) (hC : 0 ≤ C)
    (hb : A.TensorWeightedBound s m (δ^2*C) (inducedTensor F-target)) :
    A.TensorWeightedBound s m C
      (normalizedTensorDefect target δ (Real.sqrt (1-δ^2) • F)-target) := by
  have he : normalizedTensorDefect target δ (Real.sqrt (1-δ^2) • F)-target =
      (1-(δ^2)⁻¹) • (inducedTensor F-target) := by
    rw [normalizedTensorDefect_initial hF target hδ hδ1]
    abel
  rw [he]
  have hh := A.tensorWeightedBound_const_smul
    ((A.inducedTensor_smooth hF).sub_section htarget) hb (1-(δ^2)⁻¹)
  intro i
  exact (hh i).mono_const (initial_normalized_coefficient_bound hδ hδ1 hC)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InitialInputBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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
local instance initialBoundFiberNormed_r097d1e_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_r097d1e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialBoundDualSmul_r097d1e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialBoundSectionNormed_r097d1e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_r097d1e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [IsManifold planeModel ∞ M] [CompactSpace M] in
lemma space_smul_contMDiff {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (a : ℝ) :
    ContMDiff planeModel spaceModel ∞ (a • F) :=
  (a • ContinuousLinearMap.id ℝ Space).contDiff.contMDiff.comp hF

namespace SmoothingAtlas
local instance initialBoundFiberNormed_r097d1e_2 : NormedAddCommGroup TensorFiber := inferInstance
local instance initialBoundFiberSpace_r097d1e_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialBoundDualSmul_r097d1e_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance initialBoundSectionNormed_r097d1e_2 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialBoundSectionSpace_r097d1e_2 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma weightedBound_const_smul {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C : ℝ} {m : ℕ}
    (hb : A.WeightedBound s m C F) (a : ℝ) :
    A.WeightedBound s m (|a| * C) (a • F) := by
  intro i
  rw [localize_smul]
  exact (hb i).const_smul uniqueDiffOn_univ
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF).contDiffOn a

lemma shiftedBound_smul_of_abs_le_one {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) {s C a : ℝ} {q m : ℕ}
    (_hs : 0 ≤ s) (hC : 0 ≤ C) (ha : |a| ≤ 1)
    (hb : A.ShiftedBound q m s C F) : A.ShiftedBound q m s C (a • F) := by
  intro i j hj x
  have hf := localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hF
  change s^(j-q)*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) (a • F)) x‖ ≤ C
  rw [localize_smul,iteratedFDeriv_const_smul_apply (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt,
    norm_smul,Real.norm_eq_abs]
  calc
    _ = |a| * (s^(j-q)*‖iteratedFDeriv ℝ j (localize (i : M) (A.weight i) F) x‖) := by ring
    _ ≤ |a| * C := mul_le_mul_of_nonneg_left (hb i j hj x) (abs_nonneg a)
    _ ≤ C := by nlinarith

omit [CompactSpace M] in
lemma shifted_zero_to_weighted {F : M → Space} {P : ℝ} {q : ℕ}
    (hb : A.ShiftedBound q 0 1 P F) : A.WeightedBound 1 q P F := by
  intro i j hj x _
  have hh := hb i j (by omega) x
  simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hh

/-- The contracted initial map has the required two-derivative prefix and
finite high-order input bound. -/
theorem contracted_initial_input_scaled
    {F : M → Space} (hF : ContMDiff planeModel spaceModel ∞ F)
    {g : SmoothMetric M} {δ s σ P Q C D e B : ℝ} {m : ℕ}
    (hδ : δ ≠ 0) (hδ1 : δ^2 ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) (hσ : 0 < σ) (hsσ : s ≤ σ)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hmap0 : A.ShiftedBound 2 0 σ P F) (hmap : A.ShiftedBound 2 m σ C F)
    (hmetric0 : A.TensorWeightedBound 1 0 Q g.inner)
    (hmetric : A.TensorWeightedBound 1 m D g.inner)
    (herror : A.TensorWeightedBound s m (δ^2*e) (inducedTensor F-g.inner))
    (hMB : P+(s/σ)*C ≤ B) (hHB : Q+s*D+e ≤ B) :
    A.InputBound s m B (Real.sqrt (1-δ^2) • F)
      (normalizedTensorDefect g.inner δ (Real.sqrt (1-δ^2) • F)) := by
  have hsqrt : |Real.sqrt (1-δ^2)| ≤ 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (sub_nonneg.mpr hδ1),Real.sqrt_nonneg (1-δ^2),sq_nonneg δ]
  have hbF := A.shiftedBound_smul_of_abs_le_one hF hs
    (add_nonneg hP (mul_nonneg (div_nonneg hs hσ.le) hC)) hsqrt
    (A.shifted_shrink_with_prefix hmap0 hmap hσ hs hsσ hP hC)
  have hbH := A.normalized_initial_error_bound hF g.contMDiff hδ hδ1 he herror
  have hh := A.tensorWeightedBound_add g.contMDiff
    ((A.normalizedTensorDefect_smooth g.contMDiff δ (space_smul_contMDiff hF (Real.sqrt (1-δ^2)))).sub_section g.contMDiff)
    hs (A.tensor_shrink_with_norm hs hs1 hD hmetric0 hmetric) hbH
  have hid : g.inner+(normalizedTensorDefect g.inner δ (Real.sqrt (1-δ^2) • F)-g.inner) =
      normalizedTensorDefect g.inner δ (Real.sqrt (1-δ^2) • F) := by abel
  rw [hid] at hh
  exact ⟨fun i j hj x => (hbF i j hj x).trans hMB,fun i => (hh i).mono_const hHB⟩

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
local instance initialStageFiberSpace_r097d1e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialStageDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance initialStageDualSmul_r097d1e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space} {d : CorrectionGeometry g F}
namespace PreparedCorrection

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.initialStageFiberNormed
local instance initialStageFiberSpace_r097d1e_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance initialStageDualSmul_r097d1e_2 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance initialStageSectionNormed_r097d1e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance initialStageSectionSpace_r097d1e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- All conditions refer only to the original immersion through order 442
and its metric error through order 440. The first corrected map is the
specified scalar contraction, with no existence hypothesis on a sequence. -/
theorem initial_stage_of_scaled_bounds (c : PreparedCorrection d)
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {t σ P Q C D e : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/32) (htε : t < c.ε 0)
    (hσ : 0 < σ) (htσ : t ≤ σ)
    (hP : 0 ≤ P) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 ≤ e)
    (hmap0 : d.A.ShiftedBound 2 0 1 P F) (hmap : d.A.ShiftedBound 2 440 σ C F)
    (hmetric0 : d.A.TensorWeightedBound 1 0 Q g.inner)
    (hmetric : d.A.TensorWeightedBound 1 440 D g.inner)
    (herror : d.A.TensorWeightedBound t 440 ((t^(10 : ℝ))^2*e) (inducedTensor F-g.inner))
    (hMB : P+(t/σ)*C ≤ c.budget) (hHB : Q+t*D+e ≤ c.budget)
    (hnear : (t^(10 : ℝ))^2*P ≤ c.ρ/8) (hemetric : e ≤ c.a/8) :
    ∃ seed : c.Stage t 0, seed.map = Real.sqrt (1-(t^(10 : ℝ))^2) • F := by
  let δ := t^(10 : ℝ)
  let G := Real.sqrt (1-δ^2) • F
  have ht1 : t ≤ 1 := by linarith
  have hδ : 0 < δ := Real.rpow_pos_of_pos ht _
  have hδle : δ ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hδsq : δ^2 ≤ 1 := pow_le_one₀ hδ.le hδle
  have hG : ContMDiff planeModel spaceModel ∞ G := space_smul_contMDiff hF _
  have hmap0σ : d.A.ShiftedBound 2 0 σ P F := by
    intro i j hj x
    have hj2 : j - 2 = 0 := by omega
    simpa only [hj2,pow_zero,one_mul] using hmap0 i j hj x
  have hin := d.A.contracted_initial_input_scaled hF (ne_of_gt hδ) hδsq ht.le ht1
    hσ htσ hP hC hD he hmap0σ hmap hmetric0 hmetric herror hMB hHB
  have hdisp : d.A.WeightedBound 1 2 (c.ρ/8) (G-F) := by
    have hbase := d.A.shifted_zero_to_weighted hmap0
    have hh := d.A.weightedBound_const_smul hF hbase (Real.sqrt (1-δ^2)-1)
    have hid : G-F = (Real.sqrt (1-δ^2)-1) • F := by
      dsimp [G]
      rw [sub_smul,one_smul]
    rw [hid]
    intro i
    apply (hh i).mono_const
    exact (mul_le_mul_of_nonneg_right (initial_contraction_displacement hδsq) hP).trans hnear
  have hdef := d.A.normalized_initial_error_bound hF g.contMDiff
    (ne_of_gt hδ) hδsq he herror
  have hencoded := d.A.tensorEncode_bound
    ((d.A.normalizedTensorDefect_smooth g.contMDiff δ hG).sub_section g.contMDiff)
    ht he (fun i => (hdef i).mono_order (show 0 ≤ 440 from Nat.zero_le _))
  have hm : ∀ x, ‖d.A.tensorEncode (normalizedTensorDefect g.inner δ G) x-
      d.A.tensorEncode g.inner x‖ ≤ c.a/8 := by
    intro x
    have hh := (hencoded.norm_le (mem_univ x)).trans hemetric
    simpa only [d.A.tensorEncode_sub,Pi.sub_apply] using hh
  refine ⟨⟨0,G,hG,?_,?_,?_,?_⟩,rfl⟩
  · exact htε
  · simpa only [ExactCorrection.correctionScale,correctionInputOrder,correctionOrder,
      Nat.zero_add,Nat.cast_ofNat,show 40*(10+1) = 440 from rfl] using hin
  · simpa only [stageRadius,Finset.range_zero,Finset.sum_empty,mul_zero,add_zero] using hdisp
  · simpa only [ExactCorrection.correctionScale,correctionOrder,Nat.zero_add,Nat.cast_ofNat] using hm


end PreparedCorrection
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_InitializationPowers
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The strict powers needed by the initialization in exact-correction.tex. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection

/-- With the paper's initial amplitude `δ = z^(10*μ)`, contraction of a
map of C² size `O(z⁻²)` is smaller than the radius `z⁴`. An input metric
error of order `N > 20*μ` becomes small after normalization by `δ²`. -/
theorem initialization_power_threshold {μ N C a : ℝ} (hμ : 1 < μ)
    (hN : 20*μ < N) (ha : 0 < a) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z : ℝ, 0 < z → z < η →
      C*z^(20*μ-2) ≤ z^4/8 ∧ C*z^(N-20*μ) < a := by
  obtain ⟨η₁,hη₁,hη₁1,h₁⟩ := positive_power_threshold C (20*μ-6) (1/8)
    (by linarith) (by norm_num)
  obtain ⟨η₂,hη₂,_,h₂⟩ := positive_power_threshold C (N-20*μ) a
    (by linarith) ha
  refine ⟨min η₁ η₂,lt_min hη₁ hη₂,(min_le_left _ _).trans hη₁1,?_⟩
  intro z hz hzη
  refine ⟨?_,h₂ z hz (hzη.trans_le (min_le_right _ _))⟩
  have hh := mul_le_mul_of_nonneg_right (h₁ z hz (hzη.trans_le (min_le_left _ _))).le
    (pow_nonneg hz.le 4)
  have he : C*z^(20*μ-2) = (C*z^(20*μ-6))*z^4 := by
    rw [show 20*μ-2 = (20*μ-6)+4 by ring,Real.rpow_add hz,Real.rpow_ofNat]
    ring
  rw [he]
  linarith

/-- The finite first-block input budget in the paper's original weighted
scale. No loss proportional to the differentiation order is introduced. -/
theorem initialization_budget_threshold {μ N C D e : ℝ} (hμ : 1 < μ)
    (hN : 20*μ < N) (hC : 0 ≤ C) (hD : 0 ≤ D) (he : 0 < e) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1/32 ∧ ∀ z : ℝ, 0 < z → z < η →
      z^μ ≤ z ∧ z^μ ≤ 1/32 ∧
      C/z^2+(z^μ/z)*(C/z^2) ≤ 1/z^4 ∧
      D+z^μ*D+e ≤ 1/z^4 ∧
      z^(20*μ)*(C/z^2) ≤ z^4/8 ∧
      C*z^N ≤ z^(20*μ)*e := by
  obtain ⟨η₀,hη₀,_,hp⟩ := initialization_power_threshold (C := C) hμ hN he
  obtain ⟨η₁,hη₁,_,h₁⟩ := positive_power_threshold (2*C) 2 1 (by norm_num) zero_lt_one
  obtain ⟨η₂,hη₂,_,h₂⟩ := positive_power_threshold (2*D+e) 4 1 (by norm_num) zero_lt_one
  let η := min (1/32) (min η₀ (min η₁ η₂))
  refine ⟨η,lt_min (by norm_num) (lt_min hη₀ (lt_min hη₁ hη₂)),min_le_left _ _,?_⟩
  intro z hz hzη
  have hz32 : z ≤ 1/32 := hzη.le.trans (min_le_left _ _)
  have hz1 : z ≤ 1 := by linarith
  have hη := hzη.trans_le (min_le_right _ _)
  have hz₀ : z < η₀ := hη.trans_le (min_le_left _ _)
  have hη' := hη.trans_le (min_le_right _ _)
  have hz₁ : z < η₁ := hη'.trans_le (min_le_left _ _)
  have hz₂ : z < η₂ := hη'.trans_le (min_le_right _ _)
  have ht : z^μ ≤ z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hz hz1 hμ.le
  have hratio : z^μ/z ≤ 1 := (div_le_one hz).mpr ht
  have hsmall₁ : (2*C)*z^2 ≤ 1 := by
    simpa only [Real.rpow_ofNat] using (h₁ z hz hz₁).le
  have hsmall₂ : (2*D+e)*z^4 ≤ 1 := by
    simpa only [Real.rpow_ofNat] using (h₂ z hz hz₂).le
  have hbudget : 2*C/z^2 ≤ 1/z^4 := by
    apply (div_le_div_iff₀ (pow_pos hz 2) (pow_pos hz 4)).mpr
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall₁) (sq_nonneg z)]
  have hmetric : 2*D+e ≤ 1/z^4 := (le_div_iff₀ (pow_pos hz 4)).mpr hsmall₂
  obtain ⟨hdisp,herr⟩ := hp z hz hz₀
  have hpower : z^(20*μ)*(C/z^2) = C*z^(20*μ-2) := by
    rw [Real.rpow_sub hz,Real.rpow_ofNat]
    ring
  have herror : C*z^N = (C*z^(N-20*μ))*z^(20*μ) := by
    rw [mul_assoc,← Real.rpow_add hz]
    congr 2
    ring
  refine ⟨ht,ht.trans hz32,?_,?_,?_,?_⟩
  · calc
      C/z^2+(z^μ/z)*(C/z^2) ≤ C/z^2+1*(C/z^2) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hratio (div_nonneg hC (sq_nonneg z)))
      _ = 2*C/z^2 := by ring
      _ ≤ 1/z^4 := hbudget
  · exact (by nlinarith [mul_le_mul_of_nonneg_right (ht.trans hz1) hD] :
      D+z^μ*D+e ≤ 2*D+e).trans hmetric
  · rwa [hpower]
  · rw [herror]
    exact (mul_le_mul_of_nonneg_right herr.le (Real.rpow_nonneg hz.le _)).trans_eq (mul_comm _ _)

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialPreparedInitialization
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initialization at a power of the primitive scale, after all geometric
polynomial losses and before the primitive accuracy order are chosen. -/
noncomputable section
namespace ClosedSurfaceR4.ExactCorrection
open RealModes

theorem polynomial_prepared_initialization (E : ℝ → ℝ) (hE : HasPolynomialBound E) :
    ∃ ν : ℝ, 1 < ν ∧ ∃ N : ℕ, ∀ B D e r K : ℝ,
      0 ≤ B → 0 ≤ D → 0 < e → 1 ≤ r → 0 < K →
      ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z : ℝ, 0 < z → z < η →
        z^ν ≤ z ∧ z^ν ≤ 1/32 ∧
        (∀ ε : ℝ, 0 < ε → ε⁻¹ ≤ E ((z^2)⁻¹) → z^ν < ε) ∧
        B/z^2+(z^ν/z)*(B/z^2) ≤ 1/z^4 ∧
        D+z^ν*D+e ≤ 1/z^4 ∧
        ((z^ν)^(10 : ℝ))^2*(B/z^2) ≤ (z^8/r)/8 ∧
        B*z^(N+1) ≤ ((z^ν)^(10 : ℝ))^2*e ∧
        ((z^ν)^(10 : ℝ))^2*(B/z^2)+2*(z^8/r)*z^ν ≤ z^8/K := by
  obtain ⟨d,hd⟩ := hE.at_inverse_scale 2
  obtain ⟨C,hC,hbound⟩ := hd 1 le_rfl
  let ν : ℝ := (d : ℝ)+2
  have hν : 1 < ν := by dsimp [ν] <;> linarith [show (0:ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
  obtain ⟨N,hN⟩ := exists_nat_gt (20*ν)
  have hN' : 20*ν < (N : ℝ)+1 := by linarith
  refine ⟨ν,hν,N,?_⟩
  intro B D e r K hB hD he hr hK
  have hrp : 0 < r := zero_lt_one.trans_le hr
  obtain ⟨ηb,hηb,hηb32,hbudget⟩ := initialization_budget_threshold hν hN' hB hD he
  obtain ⟨ηe,hηe,_,heps⟩ := positive_power_threshold C (ν-d) 1 (by dsimp [ν] <;> linarith) zero_lt_one
  let a := min (1/(8*r)) (1/(2*K))
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  obtain ⟨ηp,hηp,_,hnear⟩ := positive_power_threshold B (20*ν-10) a (by linarith) ha
  obtain ⟨ηt,hηt,_,htail⟩ := positive_power_threshold (2/r) ν (1/(2*K)) (by linarith) (by positivity)
  let η := min ηb (min ηe (min ηp ηt))
  refine ⟨η,lt_min hηb (lt_min hηe (lt_min hηp hηt)),
    (min_le_left _ _).trans (hηb32.trans (by norm_num)),?_⟩
  intro z hz hzη
  have hzb : z < ηb := hzη.trans_le (min_le_left _ _)
  have hze : z < ηe := hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzp : z < ηp := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hzt : z < ηt := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hz1 : z ≤ 1 := hzη.le.trans ((min_le_left _ _).trans (hηb32.trans (by norm_num)))
  obtain ⟨htz,ht32,hMB,hHB,_,herr⟩ := hbudget z hz hzb
  have hδ : ((z^ν)^(10 : ℝ))^2 = z^(20*ν) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (Real.rpow_nonneg hz.le _),← Real.rpow_mul hz.le]
    congr 1
    norm_num
    ring
  have hdisp : z^(20*ν)*(B/z^2) = (B*z^(20*ν-10))*z^8 := by
    rw [Real.rpow_sub hz,Real.rpow_ofNat]
    have hp : z^10 = z^2*z^8 := by ring
    rw [hp]
    field_simp
  have hsmall := mul_le_mul_of_nonneg_right (hnear z hz hzp).le (pow_nonneg hz.le 8)
  have hsmallr : z^(20*ν)*(B/z^2) ≤ (z^8/r)/8 := by
    rw [hdisp]
    calc
      _ ≤ a*z^8 := hsmall
      _ ≤ (1/(8*r))*z^8 := mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hz.le _)
      _ = (z^8/r)/8 := by ring
  have hsmallK : z^(20*ν)*(B/z^2) ≤ z^8/(2*K) := by
    rw [hdisp]
    exact hsmall.trans (by
      calc
        a*z^8 ≤ (1/(2*K))*z^8 := mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_nonneg hz.le _)
        _ = z^8/(2*K) := by ring)
  have htailK : 2*(z^8/r)*z^ν ≤ z^8/(2*K) := by
    have hh := mul_le_mul_of_nonneg_right (htail z hz hzt).le (pow_nonneg hz.le 8)
    first | (convert hh using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
  refine ⟨htz,ht32,?_,hMB,hHB,?_,?_,?_⟩
  · intro ε hε hεb
    have hEbound : E ((z^2)⁻¹) ≤ C/z^d := by
      simpa only [one_div] using (hbound z hz hz1).2
    have heq : z^ν*(C/z^d) = C*z^(ν-d) := by
      rw [Real.rpow_sub hz,Real.rpow_natCast]
      ring
    have hh : z^ν*ε⁻¹ < 1 := (mul_le_mul_of_nonneg_left (hεb.trans hEbound)
      (Real.rpow_nonneg hz.le _)).trans_lt (by rw [heq]; exact heps z hz hze)
    exact (div_lt_one hε).mp (by simpa only [div_eq_mul_inv] using hh)
  · rwa [hδ]
  · rw [hδ]
    have hexp : (N : ℝ)+1 = ((N+1 : ℕ) : ℝ) := by norm_num
    simpa only [hexp,Real.rpow_natCast] using herr
  · rw [hδ]
    calc
      _ ≤ z^8/(2*K)+z^8/(2*K) := add_le_add hsmallK htailK
      _ = z^8/K := by ring

end ClosedSurfaceR4.ExactCorrection

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_RescaledReadBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A square of the fast scale gives a uniform low-order geometric budget. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.WeightedEstimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma WeightedBound.square_scale {f : E → V} {z B C : ℝ} {m : ℕ}
    (hb : WeightedBound univ z m C f) (hzero : WeightedBound univ 1 0 B f)
    (hz : 0 < z) (hz1 : z ≤ 1) (hC : 0 ≤ C) (hsmall : C*z ≤ 1) :
    WeightedBound univ (z^2) m (B+1) f := by
  have hB : 0 ≤ B := (norm_nonneg (f 0)).trans (hzero.norm_le (mem_univ 0))
  intro j hj x hx
  by_cases hj0 : j = 0
  · subst j
    simpa only [pow_zero,one_mul,norm_iteratedFDerivWithin_zero] using
      (hzero.norm_le hx).trans (le_add_of_nonneg_right zero_le_one)
  · have hj1 : 1 ≤ j := by omega
    have hp : z^j ≤ z := by
      simpa only [pow_one] using pow_le_pow_of_le_one hz.le hz1 hj1
    calc
      (z^2)^j*‖iteratedFDerivWithin ℝ j f univ x‖ =
          z^j*(z^j*‖iteratedFDerivWithin ℝ j f univ x‖) := by rw [pow_two,mul_pow]; ring
      _ ≤ z^j*C := mul_le_mul_of_nonneg_left (hb j hj x hx) (pow_nonneg hz.le _)
      _ ≤ z*C := mul_le_mul_of_nonneg_right hp hC
      _ ≤ 1 := by simpa only [mul_comm] using hsmall
      _ ≤ B+1 := by linarith

end ClosedSurfaceR4.WeightedEstimates
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem uniform_rescaled_read_bound (V₀ : ℝ) (hV₀ : 0 ≤ V₀) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ C : ℝ, 0 ≤ C → ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
    ∀ z : ℝ, 0 < z → z < η → ∀ F : M → Space,
      ContMDiff planeModel spaceModel ∞ F → A.WeightedBound 1 0 V₀ F →
      A.WeightedBound z 3 C F → ∀ i,
      WeightedEstimates.WeightedBound univ (z^2) 3 B
        (spaceCoordinates ∘ A.vectorPlaneRead i F) := by
  classical
  choose D₀ hD₀ hd₀ using fun i => A.vectorPlaneRead_bound (V := Space) i 0
  choose D₃ hD₃ hd₃ using fun i => A.vectorPlaneRead_bound (V := Space) i 3
  let L := ‖spaceCoordinates.toContinuousLinearMap‖
  let B := 1+∑ i : A.centers, L*D₀ i*V₀
  let K := 1+∑ i : A.centers, L*D₃ i
  have hL : 0 ≤ L := norm_nonneg _
  have hsum₀ : 0 ≤ ∑ i : A.centers, L*D₀ i*V₀ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg hL (hD₀ i)) hV₀)
  have hsum₃ : 0 ≤ ∑ i : A.centers, L*D₃ i :=
    Finset.sum_nonneg (fun i _ => mul_nonneg hL (hD₃ i))
  refine ⟨B,by change 1 ≤ 1+∑ i : A.centers, L*D₀ i*V₀; linarith,?_⟩
  intro C hC
  obtain ⟨η,hη,hη1,hh⟩ := ExactCorrection.positive_power_threshold (K*C) 1 1
    zero_lt_one zero_lt_one
  refine ⟨η,hη,hη1,?_⟩
  intro z hz hzη F hF hzero hb i
  have hz1 := hzη.le.trans hη1
  have hread0 := (hd₀ i F 1 V₀ zero_lt_one le_rfl hV₀ hF hzero).linear
    uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hF).contDiffOn
    spaceCoordinates.toContinuousLinearMap
  have hread3 := (hd₃ i F z C hz hz1 hC hF hb).linear
    uniqueDiffOn_univ hz.le (A.vectorPlaneRead_smooth i hF).contDiffOn
    spaceCoordinates.toContinuousLinearMap
  have hiK : L*D₃ i ≤ K := by
    have hi := Finset.single_le_sum (s := Finset.univ)
      (fun j _ => mul_nonneg hL (hD₃ j)) (Finset.mem_univ i)
    change L*D₃ i ≤ 1+∑ j : A.centers, L*D₃ j
    linarith
  have hsmall : (L*(D₃ i*C))*z ≤ 1 := by
    have hh' : (K*C)*z ≤ 1 := by simpa only [Real.rpow_one] using (hh z hz hzη).le
    exact (mul_le_mul_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_right hiK hC] : L*(D₃ i*C) ≤ K*C) hz.le).trans hh'
  apply (hread3.square_scale hread0 hz hz1 (mul_nonneg hL (mul_nonneg (hD₃ i) hC)) hsmall).mono_const
  have hi := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => mul_nonneg (mul_nonneg hL (hD₀ j)) hV₀) (Finset.mem_univ i)
  change L*(D₀ i*V₀)+1 ≤ 1+∑ j : A.centers, L*D₀ j*V₀
  nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ExactFastFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Arbitrarily accurate primitive maps give an actual smooth exact metric. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exactFastFiberNormed
local instance exactFastFiberSpace_r097d1e_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance exactFastDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.exactFastFiberNormed
local instance exactFastFiberSpace_r097d1e_2 : NormedSpace ℝ TensorFiber := inferInstance
local instance exactFastDualSmul_r097d1e_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance exactFastSectionNormed_r097d1e_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance exactFastSectionSpace_r097d1e_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem exact_metric_with_property_oai (g : SmoothMetric M)
    (houter : ∀ i p, p ∈ tsupport (A.weight i) → A.outer i =ᶠ[𝓝 p] (fun _ => 1))
    (R c b V₀ : ℝ) (hc : 0 < c) (hb : 0 < b) (hV₀ : 0 ≤ V₀)
    (property : ℝ → (M → Space) → Prop)
    (hfamily : A.GeometricFastFamilyWithProperty g R c b V₀ property) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ ζ : ℝ, 0 < ζ → ∀ K : ℝ, 0 < K →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ F G : M → Space,
      ContMDiff planeModel spaceModel ∞ F ∧ property z F ∧ IsSmoothIsometricImmersion M g G ∧
      A.WeightedBound 1 2 (z^8/K) (G-F) ∧
      (∀ i, WeightedEstimates.WeightedBound univ (z^2) 3 B
        (spaceCoordinates ∘ A.vectorPlaneRead i F)) ∧
      ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
        ‖firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ ≤ R ∧
        c ≤ NormalFrame.gramDet
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).1
          (firstJetPair (spaceCoordinates ∘ A.vectorPlaneRead i F) x).2 ∧
        b ≤ ‖realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x‖ := by
  obtain ⟨B,hB,hreads⟩ := A.uniform_rescaled_read_bound V₀ hV₀
  refine ⟨B,hB,?_⟩
  intro ζ hζ
  obtain ⟨z₀,a,D,hz₀,hz₀1,ha,hD,hprep⟩ :=
    A.anchored_prepared_correction g houter R c B b hc (zero_le_one.trans hB) hb
  let P : ℝ → ℝ := fun x => x^2
  have hP : HasPolynomialBound P := polynomialBound_id.pow 2
  obtain ⟨Budget,EpsInv,hBudget,hEpsInv,hdata⟩ := hprep P P hP hP
  obtain ⟨ν,hν,N,hinit⟩ := ExactCorrection.polynomial_prepared_initialization EpsInv hEpsInv
  obtain ⟨ηf,C,Cv,hηf,hC,hCv,hf⟩ := hfamily N
  obtain ⟨Dg,hDg,hg⟩ := A.exists_bundle_bound A.tensorTriv A.tensorTriv_domain 440 g.contMDiff
  let H := max C Cv
  have hH : 0 ≤ H := hC.trans (le_max_left _ _)
  have hCH : C ≤ H := le_max_left _ _
  have hCvH : Cv ≤ H := le_max_right _ _
  obtain ⟨ηr,hηr,hηr1,hr⟩ := hreads Cv hCv
  obtain ⟨ηb,hηb,_,hbase⟩ := ExactCorrection.positive_power_threshold Cv 2 1 (by norm_num) zero_lt_one
  intro K hK
  obtain ⟨ηi,hηi,hηi1,hi⟩ := hinit H Dg (a/16) D K hH hDg (by positivity) hD hK
  let η := min z₀ (min ηf (min ηr (min ηb (min ηi ζ))))
  have hη : 0 < η := lt_min hz₀ (lt_min hηf (lt_min hηr (lt_min hηb (lt_min hηi hζ))))
  let z := η/2
  have hz : 0 < z := half_pos hη
  have hzη : z < η := half_lt_self hη
  have hzz₀ : z < z₀ := hzη.trans_le (min_le_left _ _)
  have hzf : z < ηf := hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzr : z < ηr := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hzb : z < ηb := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hziζ : z < min ηi ζ := hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hzi := hziζ.trans_le (min_le_left _ _)
  have hzζ := hziζ.trans_le (min_le_right _ _)
  have hz1 : z ≤ 1 := hzz₀.le.trans hz₀1
  have hzsq : z^2 ≤ z := by simpa only [pow_one] using pow_le_pow_of_le_one hz.le hz1 (by norm_num : 1 ≤ 2)
  obtain ⟨F,hF,hproperty,hFzero,hFwb,hFshift,herr,hgeom⟩ := hf z hz hzf
  have hFread := hr z hz hzr F hF hFzero (fun i => (hFwb i).mono_order (by omega))
  have hsmall : Cv*z^2 ≤ 1 := by
    simpa only [Real.rpow_ofNat] using (hbase z hz hzb).le
  have hFbase : A.ShiftedBound 2 0 1 (P ((z^2)⁻¹)) F := by
    intro i j hj x
    have hj0 : j-2 = 0 := by omega
    have hh := hFshift i j (by omega) x
    simp only [hj0,pow_zero,one_mul] at hh ⊢
    apply hh.trans
    change Cv/z^2 ≤ ((z^2)⁻¹)^2
    apply (div_le_iff₀ (pow_pos hz 2)).mpr
    have heq : ((z^2)⁻¹)^2*z^2 = 1/z^2 := by field_simp
    rw [heq]
    exact (le_div_iff₀ (pow_pos hz 2)).mpr hsmall
  obtain ⟨p,hpa,hprho,hpbudget,hpWish,hpε⟩ := hdata (z^2) (pow_pos hz 2)
    (hzsq.trans hzz₀.le)
    F hF hFread hgeom hFbase
  have hρ : p.ρ = z^8/D := by rw [hprho]; congr 1; ring
  have hbudget : 1/z^4 ≤ p.budget := by
    have hPval : P ((z^2)⁻¹) = 1/z^4 := by dsimp [P]; field_simp
    rw [hPval] at hpWish
    linarith [p.budget_pos]
  obtain ⟨htz,ht32,htε,hMB,hHB,hnear,herror,hcontrol⟩ := hi z hz hzi
  have ht : 0 < z^ν := Real.rpow_pos_of_pos hz _
  have ht1 : z^ν ≤ 1 := by linarith
  have hmap : A.ShiftedBound 2 440 z (H/z^2) F := by
    intro i j hj x
    exact (hFshift i j hj x).trans (div_le_div_of_nonneg_right hCvH (sq_nonneg z))
  have hmap0 : A.ShiftedBound 2 0 1 (H/z^2) F := by
    intro i j hj x
    have hj0 : j-2 = 0 := by omega
    simpa only [hj0,pow_zero,one_mul] using hmap i j (by omega) x
  have hmetric0 : A.TensorWeightedBound 1 0 Dg g.inner := fun i => (hg i).mono_order (by omega)
  have herror' : A.TensorWeightedBound (z^ν) 440 (((z^ν)^(10 : ℝ))^2*(a/16))
      (inducedTensor F-g.inner) := by
    intro i
    apply ((herr i).shrink_scale ht.le ht1).mono_const
    exact (mul_le_mul_of_nonneg_right hCH (pow_nonneg hz.le _)).trans herror
  obtain ⟨seed,hseed⟩ := p.initial_stage_of_scaled_bounds hF ht ht32
    (htε _ (p.ε_pos 0) hpε) hz htz (by positivity) (by positivity) hDg (by positivity)
    hmap0 hmap hmetric0 hg herror' (hMB.trans hbudget) (hHB.trans hbudget)
    (by rwa [hρ]) (by rw [hpa]; linarith)
  obtain ⟨G,hG,hclose⟩ := p.exact_correction_initial_displacement hF ht ht32
    (by positivity) hmap0 seed hseed
  rw [hρ] at hclose
  exact ⟨z,hz,hzζ,hz1,F,G,hF,hproperty,hG,(fun i => (hclose i).mono_const hcontrol),hFread,hgeom⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_metric_with_property_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exact_metric_with_property_oai.{u_1}
