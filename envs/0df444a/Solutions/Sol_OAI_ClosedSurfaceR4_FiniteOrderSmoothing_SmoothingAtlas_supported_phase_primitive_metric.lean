-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:49:22.609918+00:00
-- url     : https://prove2.me/submissions/83705b39-0e44-44f4-9846-2df36b24e7f3

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phaseAtlasAnsatz_error_bound
import Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_exists_bounded_coefficients
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_meanTensorPolynomial_global_extension
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_primitive_metric_remainder

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




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

end ClosedSurfaceR4.WeightedEstimates

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_MeanSupport
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

namespace ClosedSurfaceR4.WeightedEstimates
open Set
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




lemma WeightedBound.extend_support {U : Set E} (hU : IsOpen U) {f : E → F}
    (hfs : tsupport f ⊆ U) {s C : ℝ} {m : ℕ} (hC : 0 ≤ C)
    (hb : WeightedBound U s m C f) : WeightedBound univ s m C f := by
  intro j hj x hx
  rw [iteratedFDerivWithin_univ]
  by_cases hxU : x ∈ U
  · rw [← iteratedFDerivWithin_of_isOpen j hU hxU]
    exact hb j hj x hxU
  · have hz : f =ᶠ[nhds x] 0 := notMem_tsupport_iff_eventuallyEq.mp (fun hh => hxU (hfs hh))
    rw [(hz.iteratedFDeriv ℝ j).self_of_nhds]
    simpa using hC

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothingTransition
attribute [-instance] _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorTriv_mem _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate transitions that transport each localized smoothing error. -/
noncomputable section
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open Set Manifold WeightedEstimates
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [CompactSpace M] in
/-- Writing a restored component in another chart is multiplication by a
fixed smooth weight followed by the fixed transition. -/
lemma localize_restore (i j : A.centers) (h : Base → V) :
    localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h) =
      fun x => A.pairWeight i j x • h (transition (i : M) (j : M) x) := by
  funext x
  by_cases hi : x ∈ (chart (i : M)).target
  · by_cases hj : (chart (i : M)).symm x ∈ (chart (j : M)).source
    · simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_mem hj]
      rw [smul_smul]
      rfl
    · have hz : A.outer j ((chart (i : M)).symm x) = 0 :=
        image_eq_zero_of_notMem_tsupport (fun hp => hj (A.outer_support j hp))
      simp only [localize, restore, pairWeight, indicator_of_mem hi, indicator_of_notMem hj,
        hz, smul_zero, zero_smul]
  · simp only [localize, pairWeight, indicator_of_notMem hi, zero_smul]

/-- Each overlap transports a global weighted bound with fixed constants. -/
theorem pair_weighted_bound (i j : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ h → _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m C h →
      _root_.OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound Set.univ s m (D * C)
        (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) h)) := by
  obtain ⟨D, hD, hb⟩ := compact_localized_composition_bound (V := V)
    (transition (i : M) (j : M)).open_source (A.pairSupport_compact i j)
    (A.pairSupport_transition i j) (A.pairWeight_smooth i j) (A.pairWeight_support i j)
    (transition_smooth (i : M) (j : M)) m
  refine ⟨D, hD, ?_⟩
  intro h s C hs hs1 hC hh hbh
  rw [A.localize_restore]
  exact hb h s C hs hs1 hC hh hbh

end SmoothingAtlas
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

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

variable [CompactSpace M]

/-- Restoring finitely many coordinate functions is bounded in every fixed
weighted atlas norm, uniformly in the input and the scale. -/
theorem restoration_bound (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (h : A.centers → Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → (∀ i, ContDiff ℝ ∞ (h i)) →
      (∀ i, WeightedEstimates.WeightedBound Set.univ s m C (h i)) →
      A.WeightedBound s m (D * C) (∑ i : A.centers, restore (i : M) (A.outer i) (h i)) := by
  classical
  choose D hD hbound using fun i j : A.centers => A.pair_weighted_bound (V := V) i j m
  refine ⟨∑ i : A.centers, ∑ j : A.centers, D i j,
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hD i j)), ?_⟩
  intro h s C hs hs1 hC hh hb i
  have hf (j : A.centers) : ContDiff ℝ ∞
      (localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j))) :=
    localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i)
      (restore_smooth (j : M) (A.outer_smooth j) (A.outer_support j) (hh j))
  have hsum := WeightedEstimates.WeightedBound.finset_sum uniqueDiffOn_univ hs.le
    (Finset.univ : Finset A.centers) (fun j => D i j * C)
    (fun j => localize (i : M) (A.weight i) (restore (j : M) (A.outer j) (h j)))
    (fun j _ => (hf j).contDiffOn)
    (fun j _ => hbound i j (h j) s C hs hs1 hC (hh j) (hb j))
  rw [localize_sum]
  apply hsum.mono_const
  rw [← Finset.sum_mul]
  apply mul_le_mul_of_nonneg_right _ hC
  exact Finset.single_le_sum
    (fun k _ => Finset.sum_nonneg (fun j _ => hD k j)) (Finset.mem_univ i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedChartPullback
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported pullback through a local chart, extended by a fixed
cutoff without altering the pullback on the chart's source. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma supportedChartPullback_smooth (e : OpenPartialHomeomorph Base Base)
    {χ : Base → ℝ} {f : Base → V} (he : ContDiff ℝ ∞ e)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (supportedChartPullback e χ f) := hχ.smul (hf.comp he)

lemma supportedChartPullback_bound (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) {χ : Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcompact : HasCompactSupport χ) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : Base → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContDiff ℝ ∞ f →
      WeightedEstimates.WeightedBound univ s m C f →
      WeightedEstimates.WeightedBound univ s m (D*C) (supportedChartPullback e χ f) :=
  compact_localized_composition_bound isOpen_univ hcompact (subset_univ _)
    hχ (Subset.rfl) he.contDiffOn m

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_SmoothPeriodicPrimitive
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.SmoothPeriodicCalculus.primitiveFamily_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Jointly smooth normalized primitives with parameters. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma primitive_zero (x : ℝ) : primitive (fun _ : ℝ => (0 : E)) x = 0 := by
  simp [primitive, rawPrimitive]

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Periodic differentiation and integration on an open parameter domain. -/

noncomputable section
open MeasureTheory
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicCalculus

open CovarianceCorrector SmoothPeriodicCalculus

variable {P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ P] [CompleteSpace E]

lemma primitiveOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    primitiveOn F S hS hF hm p (t : Period) =
      PeriodicPrimitive.primitive (fun s => F p (s : Period)) t :=
  bundleOn_apply _ _ _ _ _ hp t

lemma primitiveOn_zero_at (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (hz : F p = 0) :
    primitiveOn F S hS hF hm p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro t
  rw [primitiveOn_apply F S hS hF hm hp, hz]
  exact PeriodicPrimitive.primitive_zero t

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilyAlgebra
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Algebra and support preservation for periodic families on an open domain. -/
noncomputable section

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {O : TopologicalSpace.Opens A} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ A] [CompleteSpace E]

lemma primitive_zero_at (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0)
    {p : A} (hp : p ∈ O) (hz : F.val p = 0) : (F.primitive hm).val p = 0 := by
  have he : (F.primitive hm).val p = primitiveOn F.val O O.isOpen F.smooth hm p := by
    ext t
    exact ofLocal_apply _ _ hp _
  rw [he]
  exact primitiveOn_zero_at _ _ _ _ _ hp hz

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicGlobalization
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compactly supported local periodic coefficients extend smoothly by zero. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma finiteAnsatz_smooth_global {F : A → E} (hF : ContDiff ℝ ∞ F)
    (U : ℕ → Family O E) {K : Set A} (hK : IsClosed K) (hKO : K ⊆ O)
    (hz : ∀ i p, p ∈ O → p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (finiteAnsatz F U ℓ L z) := by
  apply hF.add
  apply ContDiff.sum
  intro i _
  exact contDiff_const.smul (((U i).smooth_global hK hKO (hz i)).comp
    (contDiff_id.prodMk (ℓ.contDiff.div_const z)))

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma finiteAnsatz_eq_off_support (F : A → E) (U : ℕ → Family O E)
    {K : Set A} (hz : ∀ i p, p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {p : A} (hp : p ∉ K) :
    finiteAnsatz F U ℓ L z p = F p := by
  simp only [finiteAnsatz, Family.fastValue, hz _ p hp, ContinuousMap.zero_apply,
    smul_zero, Finset.sum_const_zero, add_zero]

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalAnsatzSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact support and exact boundary jets of the actual finite ansatz. -/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {O : TopologicalSpace.Opens A}

lemma finiteAnsatz_tsupport_sub (F : A → E) (U : ℕ → Family O E)
    {K : Set A} (hK : IsClosed K) (hzero : ∀ i p, p ∉ K → (U i).val p = 0)
    (ℓ : A →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    tsupport (fun p => finiteAnsatz F U ℓ L z p-F p) ⊆ K := by
  apply closure_minimal _ hK
  intro p hp
  by_contra hpK
  apply (Function.mem_support.mp hp)
  rw [finiteAnsatz_eq_off_support F U hzero ℓ L z hpK,sub_self]

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPrimitiveMapBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The same compactly supported local increment controls the derivatives
of its actual global restoration. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial LocalPeriodicExpansion WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem single_map_restore_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (f : JetPolynomial.Base → Space), ContDiff ℝ ∞ f →
      ∀ (s C : ℝ), 0 < s → s ≤ 1 → 0 ≤ C →
      WeightedEstimates.WeightedBound univ s m C f →
      A.WeightedBound s m (D*C) (restore (i : M) (A.outer i) f) := by
  classical
  obtain ⟨D,hD,hd⟩ := A.restoration_bound (V := Space) m
  refine ⟨D,hD,?_⟩
  intro f hf s C hs hs1 hC hb
  have hh := hd (fun j => if j = i then f else 0) s C hs hs1 hC
    (by intro j; split_ifs; exact hf; exact contDiff_const)
    (by
      intro j
      split_ifs
      · exact hb
      · exact (weightedBound_zero _ s m).mono_const hC)
  have he : (∑ j : A.centers, restore (j : M) (A.outer j) (if j = i then f else 0)) =
      restore (i : M) (A.outer i) f := by
    funext p
    rw [Finset.sum_apply,Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji,restore]
    · exact fun hi => False.elim (hi (Finset.mem_univ _))
  rw [he] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasAnsatz
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported finite ansatz in a nonlinear phase chart, restored to the
original surface and retaining its exact coordinate expression. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseAtlasLocalIncrement_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContDiff ℝ ∞ (A.phaseAtlasLocalIncrement i F e χ U ℓ L z) := by
  have hG := (A.vectorChartRead_smooth i hF).comp hi
  exact supportedChartPullback_smooth e he hχ
    ((finiteAnsatz_smooth_global hG U hK hKO (fun j x _ hx => hzero j x hx) ℓ L z).sub hG)

lemma phaseAtlasAnsatz_smooth (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsClosed K) (hKO : K ⊆ O)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    ContMDiff planeModel spaceModel ∞ (A.phaseAtlasAnsatz i F e χ U ℓ L z) :=
  hF.add (restore_smooth (i : M) (A.outer_smooth i) (A.outer_support i)
    (A.phaseAtlasLocalIncrement_smooth i hF e he hi hχ U hK hKO hzero ℓ L z))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasMapBound
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed coordinate transport of the actual periodic map increment. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial LocalPeriodicExpansion WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phaseAtlasAnsatz_increment_bound (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
    ∀ (S : TopologicalSpace.Opens JetPolynomial.Base) (U : ℕ → Family S Space)
      (K : Set JetPolynomial.Base), IsClosed K → K ⊆ S →
      (∀ j x, x ∉ K → (U j).val x = 0) →
    ∀ (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C →
      WeightedEstimates.WeightedBound S s m C
        (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z-A.vectorChartRead i F ∘ e.symm) →
      A.WeightedBound s m (D*C) (A.phaseAtlasAnsatz i F e χ U ℓ L z-F) := by
  obtain ⟨Dt,hDt,ht⟩ := supportedChartPullback_bound (V := Space) e he hχ hc m
  obtain ⟨Dr,hDr,hr⟩ := A.single_map_restore_bound i m
  refine ⟨Dr*Dt,mul_nonneg hDr hDt,?_⟩
  intro F hF S U K hK hKS hzero ℓ L z s C hs hs1 hC hb
  let f := finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z-A.vectorChartRead i F ∘ e.symm
  have hbase := (A.vectorChartRead_smooth i hF).comp hi
  have hf : ContDiff ℝ ∞ f :=
    (finiteAnsatz_smooth_global hbase U hK hKS (fun j x _ hx => hzero j x hx) ℓ L z).sub hbase
  have hsp : tsupport f ⊆ S := (finiteAnsatz_tsupport_sub _ U hK hzero ℓ L z).trans hKS
  have hglobal := hb.extend_support S.isOpen hsp hC
  have hpull := ht f s C hs hs1 hC hf hglobal
  have hrest := hr (supportedChartPullback e χ f) (supportedChartPullback_smooth e he hχ hf)
    s (Dt*C) hs hs1 (mul_nonneg hDt hC) hpull
  have heq : A.phaseAtlasAnsatz i F e χ U ℓ L z-F =
      restore (i : M) (A.outer i) (supportedChartPullback e χ f) := by
    funext p
    exact add_sub_cancel_left _ _
  rw [heq]
  simpa only [mul_assoc] using hrest

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityFamily
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert a geometric second-jet velocity loop into the exact family of
Euclidean data used by the supported finite periodic recursion. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion LocalPeriodicCalculus
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

lemma euclideanVelocity_mean {J : LowJet} (hJ : J ∈ O) :
    average (l.euclideanVelocity J) = ι (normal J) := by
  rw [average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [l.euclideanVelocity_apply hJ]
  have hi : IntervalIntegrable (fun t => l.velocity (J, t)) MeasureTheory.volume 0 1 :=
    (smooth_slice O.isOpen l.smoothVelocity hJ).continuous.intervalIntegrable 0 1
  exact (JetVelocityCoordinates.toEuclidean.toContinuousLinearMap.intervalIntegral_comp_comm hi).trans
    (congrArg ι (l.mean J hJ))

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SurfaceVelocityIdentities
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The leading metric and support of the actual second-jet family. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates CovarianceCorrector
open LocalPeriodicExpansion
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

variable {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O)

lemma geometry_velocity {p : JetPolynomial.Base} (hp : p ∈ S) :
    (l.geometry G hG hGO).V.val p = l.euclideanVelocity (lowJet G p) := by
  apply ContinuousMap.ext
  intro t
  change (Family.ofLocal (fun q => l.euclideanVelocity (lowJet G q)) _).val p t = _
  exact Family.ofLocal_apply _ _ hp t

lemma geometry_mean {p : JetPolynomial.Base} (hp : p ∈ S) :
    average ((l.geometry G hG hGO).V.val p) = ι (normal (lowJet G p)) := by
  rw [l.geometry_velocity hG hGO hp]
  exact l.euclideanVelocity_mean (hGO hp)

lemma geometry_initial_zero {p : JetPolynomial.Base} (hp : p ∈ S)
    (hz : ∀ t, l.velocity (lowJet G p, t) = normal (lowJet G p)) :
    (l.geometry G hG hGO).initial.val p = 0 := by
  apply Family.primitive_zero_at _ _ hp
  apply ContinuousMap.ext
  intro t
  rw [Family.sub_apply, Family.vectorMean_apply, l.geometry_mean hG hGO hp,
    l.geometry_velocity hG hGO hp]
  refine Quotient.inductionOn' t ?_
  intro t
  rw [l.euclideanVelocity_apply (hGO hp), hz, sub_self]
  rfl

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_BoundedSurfaceCorrection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the finite periodic correction to the actual geometric second-jet
family, including global smooth extension and its uniform scale bound. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceVelocityFamily
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion
open CovarianceCorrector WeightedEstimates
local notation "ι" => JetVelocityCoordinates.toEuclidean

namespace Loop
variable {O : TopologicalSpace.Opens LowJet} (l : Loop O)

lemma yData_smooth : ContDiffOn ℝ ∞ yData O :=
  (JetVelocityCoordinates.toEuclidean.contDiff.comp (slot_smooth 2)).contDiffOn

lemma cData_smooth : ContDiffOn ℝ ∞ cData O :=
  (JetVelocityCoordinates.toEuclidean.contDiff.comp (slot_smooth 6)).contDiffOn

include l in
lemma xData_smooth : ContDiffOn ℝ ∞ xData O :=
  JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn l.smoothTangent

/-- The loss exponent is fixed by the geometric loop and finite depth,
before choosing a slow map or a differentiation order. The same coefficients
have cancellation, support, polynomial representation, and the scale bound. -/
theorem bounded_surface_correction {S : TopologicalSpace.Opens JetPolynomial.Base}
    {K : Set LowJet} (hK : IsCompact K) (hKO : K ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (hG : ContDiff ℝ ∞ G)
        (hGK : MapsTo (lowJet G) S K),
      let g := l.geometry G hG (fun _ hp => hKO (hGK hp))
      ∀ A : Set JetPolynomial.Base, IsClosed A → A ⊆ S →
        (∀ p ∈ S, p ∉ A → ∀ t, l.velocity (lowJet G p, t) = normal (lowJet G p)) →
      ∃ U : ℕ → Family S Euclidean,
        U 0 = g.initial ∧ (∀ i p, p ∈ S → average ((U i).val p) = 0) ∧
        (∀ i, ContDiff ℝ ∞ (fun z : JetPolynomial.Base × ℝ => (U i).val z.1 (z.2 : Period))) ∧
        (∀ i p, p ∉ A → (U i).val p = 0) ∧
        (g.yyCoefficient U 1).fluct = 0 ∧
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector 0) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) ∧
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) ∧
        ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
          WeightedBound S s (m + (2 * n + 2)) B (lowJet G) →
          WeightedBound S z m (D * z / s ^ d)
            (fun p => finiteAnsatz (fun q => ι (G q)) U ℓ (n + 1) z p - ι (G p)) := by
  obtain ⟨d, hd⟩ := exists_bounded_coefficients (S := S) O.isOpen hK hKO 0 1 n ℓ
    yData_smooth cData_smooth (xData_smooth l) l.euclideanVelocity_smooth
    (fun J hJ => by rw [yData, cData, gram_toEuclidean]; exact l.gram_ne J hJ)
    l.smoothQ (fun _ hJ => l.q_pos hJ) (fun _ hJ => l.euclideanVelocity_length hJ)
  refine ⟨d, ?_⟩
  intro m B hB
  obtain ⟨D, hD, hcoeff⟩ := hd m B hB
  refine ⟨D, hD, ?_⟩
  intro G hG hGK g A hA hAS hz
  obtain ⟨U, hinit, hmean, hy, hsupport, hc, hrep, hb⟩ := hcoeff G g hG hGK
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ hp => l.geometry_velocity hG (fun _ hp => hKO (hGK hp)) hp) (fun _ _ => rfl)
  have hzero : ∀ i p, p ∈ S → p ∉ A → (U i).val p = 0 := by
    intro i p hp hpA
    exact hsupport ((S : Set JetPolynomial.Base) ∩ Aᶜ)
      (S.isOpen.inter hA.isOpen_compl) inter_subset_left
      (fun q hq => l.geometry_initial_zero hG (fun _ hp => hKO (hGK hp)) hq.1 (hz q hq.1 hq.2))
      i p ⟨hp, hpA⟩
  refine ⟨U, hinit, hmean, ?_, ?_, hy, hc, hrep, ?_⟩
  · exact fun i => (U i).smooth_global hA hAS (hzero i)
  · intro i p hp
    by_cases hpS : p ∈ S
    · exact hzero i p hpS hp
    · exact (U i).outside hpS
  · intro s z hz hzs hs1 hbound
    exact hb s z hz hzs hs1 hbound (fun q => ι (G q))

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_SupportedPrimitiveExpansion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite recursion supplies the same supported coefficients for the
actual primitive and its full tensor remainder. Both losses are fixed before
the differentiation order and before the slow map. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open RealModes JetPolynomial JetVelocityCoordinates LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem supported_primitive_expansion {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (hamp : l.HasSpatialAmplitude a) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (G : JetPolynomial.Base → JetPolynomial.Space) (_hG : ContDiff ℝ ∞ G)
        (_hGQ : MapsTo (lowJet G) S Q),
      ∀ K : Set JetPolynomial.Base, IsClosed K → K ⊆ S →
        (∀ p ∈ S, p ∉ K → ∀ t, l.velocity (lowJet G p,t) = normal (lowJet G p)) →
      ∃ U : ℕ → Family S Euclidean,
        (∀ i, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U i).val y.1 (y.2 : Period))) ∧
        (∀ i p, p ∉ K → (U i).val p = 0) ∧
        (∀ i, VectorExpression.Represents G (l.coefficientExpressions n i) (U i)) ∧
        U 0 = (l.geometry G _hG (fun _ hp => hQO (_hGQ hp))).initial ∧
        ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
          WeightedBound S s (m+(2*(n+1)+1)) B (lowJet G) →
          WeightedBound S z m (C*z/s^loss)
            (fun p => finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
              U ℓ (n+1) z p-JetVelocityCoordinates.toEuclidean (G p)) ∧
          WeightedBound S z m (D*z^(n+1)/s^loss)
            (fun p => RealModes.realMetricTensor
              (spaceCoordinates ∘ finiteAnsatz (fun q => JetVelocityCoordinates.toEuclidean (G q))
                U ℓ (n+1) z ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry p)-
              l.meanTensorOperator n z G (planeCoordinateIsometry p)-![a p^2,0,0]) := by
  obtain ⟨dc,hc⟩ := l.bounded_surface_correction (S := S) hQ hQO n ℓ
  obtain ⟨de,he⟩ := l.uniform_primitive_metric_remainder (S := S) ha hamp hQ hQO n ℓ hℓx hℓy
  refine ⟨max dc de,?_⟩
  intro m B hB
  obtain ⟨C,hC,hcb⟩ := hc m B hB
  obtain ⟨D,hD,heb⟩ := he m B hB
  refine ⟨C,D,hC,hD,?_⟩
  intro G hG hGQ K hK hKS hv
  obtain ⟨U,hinit,_,hU,hzero,hy,hcoeff,hrep,hbound⟩ := hcb G hG hGQ K hK hKS hv
  refine ⟨U,hU,hzero,hrep,hinit,?_⟩
  intro s z hz hzs hs1 hb
  have hs : 0 < s := hz.trans_le hzs
  have hden (d : ℕ) (hd : d ≤ max dc de) : s^(max dc de) ≤ s^d :=
    pow_le_pow_of_le_one hs.le hs1 hd
  constructor
  · exact (hbound s z hz hzs hs1 (hb.mono_order (by omega))).mono_const
      (div_le_div_of_nonneg_left (mul_nonneg hC hz.le)
        (pow_pos hs _) (hden dc (le_max_left _ _)))
  · exact (heb G hG hGQ s z hz hzs hs1 hb U hrep hU hinit hy hcoeff).mono_const
      (div_le_div_of_nonneg_left (mul_nonneg hD (pow_nonneg hz.le _))
        (pow_pos hs _) (hden de (le_max_right _ _)))

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_NonlinearPrimitiveExpansion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact decomposition of a global primitive's metric defect into the
solved polynomial mean error and the finite periodic remainder. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionFiberNormed
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.phaseExpansionFiberSpace
local instance phaseExpansionSectionNormed_rdcc1c3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance phaseExpansionSectionSpace_rdcc1c3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- The actual finite velocity recursion in a nonlinear phase chart,
with the pulled-back polynomial mean and global supported error estimates. -/
theorem supported_phase_primitive_metric_oai (i : A.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (n : ℕ) (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0) :
    ∃ P : Fin 3 → Fin n → Expression, (∀ k r, (P k r).SmoothCoeffs univ) ∧
    ∃ loss : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ Dv D : ℝ, 0 ≤ Dv ∧ 0 ≤ D ∧
      ∀ (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
        (hGQ : MapsTo (lowJet (A.jetChartMap i G ∘ e.symm)) S Q),
      ∀ K : Set JetPolynomial.Base, IsCompact K → K ⊆ S →
      e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) →
      (∀ x ∈ e.symm '' K, χ x = 1) →
      (∀ p ∈ S, p ∉ K → ∀ t,
        l.velocity (lowJet (A.jetChartMap i G ∘ e.symm) p,t) =
          SurfaceVelocityFamily.normal (lowJet (A.jetChartMap i G ∘ e.symm) p)) →
      ∃ U : ℕ → Family S Space,
        (∀ j p, p ∉ K → (U j).val p = 0) ∧
        (∀ j, ContDiff ℝ ∞ (fun y : JetPolynomial.Base × ℝ => (U j).val y.1 (y.2 : Period))) ∧
        (∀ j, VectorExpression.Represents (A.jetChartMap i G ∘ e.symm) (l.coefficientExpressions n j) (U j)) ∧
        U 0 = (l.geometry (A.jetChartMap i G ∘ e.symm) ((A.jetChartMap_smooth i hG).comp hi)
          (fun _ hp => hQO (hGQ hp))).initial ∧
        (∀ z, ContMDiff planeModel spaceModel ∞ (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z)) ∧
      ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
        WeightedEstimates.WeightedBound S s (m+(2*(n+1)+1)) B (lowJet (A.jetChartMap i G ∘ e.symm)) →
        A.WeightedBound z m (Dv*z/s^loss) (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z-G) ∧
        ∀ (γ : ∀ x : M, CovariantTwoTensor x),
          ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
            (fun x => TotalSpace.mk' TensorFiber x (γ x)) →
        ∀ C : ℝ, A.TensorWeightedBound z m C
          (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
            (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z G-γ) →
        A.TensorWeightedBound z m (C+D*z^(n+1)/s^loss)
          (inducedTensor (A.phaseAtlasAnsatz i G e χ U ℓ (n+1) z)-
            (γ+A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
              (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))) := by
  obtain ⟨P,hP,_,_,hmean⟩ := l.meanTensorPolynomial_global_extension hQ hQO n
  obtain ⟨loss,hloss⟩ := l.supported_primitive_expansion (S := S) ha hamp hQ hQO n ℓ hℓx hℓy
  refine ⟨P,hP,loss,?_⟩
  intro m B hB
  obtain ⟨C₀,D₀,hC₀,hD₀,hconstruct⟩ := hloss m B hB
  obtain ⟨Dr,hDr,hr⟩ := A.phaseAtlasAnsatz_error_bound i e he hi hχ hχc hχs S.isOpen hTS m
  obtain ⟨Dv,hDv,hvb⟩ := A.phaseAtlasAnsatz_increment_bound i e he hi hχ hχc m
  refine ⟨Dv*C₀,Dr*D₀,mul_nonneg hDv hC₀,mul_nonneg hDr hD₀,?_⟩
  intro G hG hGQ K hK hKS hKA hone hv
  have hGj := (A.jetChartMap_smooth i hG).comp hi
  obtain ⟨U,hU,hzero,hrep,hinit,hrem⟩ := hconstruct (A.jetChartMap i G ∘ e.symm) hGj hGQ
    K hK.isClosed hKS hv
  have heuc : (fun q => JetVelocityCoordinates.toEuclidean ((A.jetChartMap i G ∘ e.symm) q)) =
      A.vectorChartRead i G ∘ e.symm := by
    funext q
    exact spaceCoordinates.symm_apply_apply _
  rw [heuc] at hrem
  refine ⟨U,hzero,hU,hrep,hinit,
    fun z => A.phaseAtlasAnsatz_smooth i hG e he hi hχ U hK.isClosed hKS hzero ℓ (n+1) z,?_⟩
  intro s z hz hzs hs1 hGb
  have hs : 0 < s := hz.trans_le hzs
  have hz1 : z ≤ 1 := hzs.trans hs1
  have hlocalIncrement := (hrem s z hz hzs hs1 hGb).1
  refine ⟨?_,?_⟩
  · have hh := hvb G hG S U K hK.isClosed hKS hzero ℓ (n+1) z z (C₀*z/s^loss)
      hz hz1 (by positivity) hlocalIncrement
    simpa only [mul_div_assoc,mul_assoc] using hh
  intro γ hγ C hsolved
  let B₀ : JetPolynomial.Base → PhaseMean.Tensor := fun q => ![a q^2,0,0]
  have hB₀ : ContDiff ℝ ∞ B₀ := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k
    · exact ha.pow 2
    · exact contDiff_const
    · exact contDiff_const
  have hlocal : WeightedEstimates.WeightedBound S z m (D₀*z^(n+1)/s^loss)
      (A.phaseAtlasRemainder i G e U ℓ (n+1) z P B₀) := by
    apply (hrem s z hz hzs hs1 hGb).2.congr
    intro p hp
    dsimp only [phaseAtlasRemainder,B₀]
    rw [hmean _ hGj z p (hGQ hp)]
  have hh := hr G hG S U K hK hKS hKA hzero hone ℓ (n+1) z n P hP γ hγ B₀ hB₀
    z C (D₀*z^(n+1)/s^loss) hz hz1 (by positivity) hsolved hlocal
  simpa only [B₀,mul_div_assoc,mul_assoc] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric_oai.{u_1}
