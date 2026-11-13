-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:49:21.283791+00:00
-- url     : https://prove2.me/submissions/7abee024-8a62-4ef5-aecc-f2c0143b0a7a

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
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_primitive_atlas_normal_margin
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_supported_patch_geometry
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_mean_approximation_in_atlas
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_phase_normal_margin
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_supported_phase_primitive_metric
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_all_orders_primitive_normal_geometry
import Theorems.Thm_OAI_ClosedSurfaceR4_SurfaceVelocityFamily_Loop_uniform_primitive_five_profiles

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

lemma WeightedBound.fderivWithin {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ} {f : E → F}
    (hs : 0 < s) (hb : WeightedBound U s (m + 1) C f) :
    WeightedBound U s m (C / s) (fderivWithin ℝ f U) := by
  intro j hj x hx
  rw [norm_iteratedFDerivWithin_fderivWithin hU hx]
  apply (le_div_iff₀ hs).2
  have hh := hb (j + 1) (Nat.add_le_add_right hj 1) x hx
  rw [pow_succ] at hh
  nlinarith

lemma WeightedBound.clm_apply_const {U : Set E} (hU : UniqueDiffOn ℝ U) {s C : ℝ} {m : ℕ}
    {f : E → F →L[ℝ] G} (hs : 0 ≤ s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s m C f) (v : F) :
    WeightedBound U s m (‖v‖ * C) (fun x => f x v) := by
  intro j hj x hx
  calc
    _ ≤ s ^ j * (‖v‖ * ‖iteratedFDerivWithin ℝ j f U x‖) := by
      gcongr
      exact norm_iteratedFDerivWithin_clm_apply_const (n := j) (N := ∞)
        (hf.contDiffWithinAt hx) hU hx (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))
    _ = ‖v‖ * (s ^ j * ‖iteratedFDerivWithin ℝ j f U x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb j hj x hx) (norm_nonneg v)




lemma WeightedBound.congr {U : Set E} {s C : ℝ} {m : ℕ} {f g : E → F}
    (hf : WeightedBound U s m C f) (he : EqOn g f U) : WeightedBound U s m C g := by
  intro j hj x hx
  rw [iteratedFDerivWithin_congr he hx]
  exact hf j hj x hx

lemma WeightedBound.directional {U : Set E} (hU : IsOpen U) {s C : ℝ} {m : ℕ}
    {f : E → F} (hs : 0 < s) (hf : ContDiffOn ℝ ∞ f U)
    (hb : WeightedBound U s (m + 1) C f) (v : E) :
    WeightedBound U s m (‖v‖ * (C / s)) (fun x => fderiv ℝ f x v) := by
  have hd := hb.fderivWithin hU.uniqueDiffOn hs
  have hdsm : ContDiffOn ℝ ∞ (_root_.fderivWithin ℝ f U) U :=
    hf.fderivWithin hU.uniqueDiffOn (by exact le_rfl)
  apply (hd.clm_apply_const hU.uniqueDiffOn hs.le hdsm v).congr
  intro x hx
  dsimp only
  rw [fderivWithin_of_isOpen hU hx]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_DirectionalJetBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Higher directional jets of a controlled second jet lose one scale per
additional derivative. These are the factors in the finite jet polynomials. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.WeightedEstimates

variable {A E : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma WeightedBound.iteratedDirectional {U : Set A} (hU : IsOpen U) {f : A → E}
    {s C : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hf : ContDiffOn ℝ ∞ f U)
    (vs : List A) (hv : ∀ v ∈ vs, ‖v‖ ≤ 1) (m : ℕ)
    (hb : WeightedBound U s (m + vs.length) C f) :
    WeightedBound U s m (C / s ^ vs.length) (iteratedDirectional vs f) := by
  induction vs generalizing m with
  | nil => simpa [ClosedSurfaceR4.WeightedEstimates.iteratedDirectional] using hb
  | cons v vs ih =>
    have he : m + (v :: vs).length = (m + 1) + vs.length := by simp; omega
    have ht := ih (fun w hw => hv w (List.mem_cons_of_mem v hw)) (m + 1) (he ▸ hb)
    have hd := ht.directional hU hs (contDiffOn_iteratedDirectional hU hf vs) v
    apply hd.mono_const
    have hn : ‖v‖ ≤ 1 := hv v (List.mem_cons_self ..)
    have hc : 0 ≤ C / s ^ vs.length / s := by positivity
    calc
      ‖v‖ * (C / s ^ vs.length / s) ≤ C / s ^ vs.length / s := mul_le_of_le_one_left hc hn
      _ = C / s ^ (v :: vs).length := by simp [pow_succ, div_div]

end ClosedSurfaceR4.WeightedEstimates

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

lemma localize_add (p : M) (ψ : M → ℝ) (f g : M → V) :
    localize p ψ (f + g) = localize p ψ f + localize p ψ g := by
  funext x
  by_cases hx : x ∈ (chart p).target <;> simp [localize, hx, smul_add]

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_WeightedActualJets
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual jets have precisely one scale loss per derivative beyond the
controlled second jet, with no loss for their first two derivatives. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma norm_coordinateVector_le (v : Fin 2) : ‖coordinateVector v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  by_cases h : i = v
  · subst i
    simp [coordinateVector]
  · simp [coordinateVector, h]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetVariations
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual variations of the ordered coordinate jets. The position entries
do not vary, and a second-jet variation costs at most two short-scale powers. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_affine {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (t : ℝ) (p : Base) :
    lowJet (fun q => G q + t • H q) p = lowJet G p + t • variationLowJet H p := by
  funext i
  cases i with
  | inl i => simp [lowJet, variationLowJet]
  | inr i =>
    change jet (fun q => G q + t • H q) (lowWord i.1) i.2 p = _
    rw [jet_add (H := fun q => t • H q) hG (ContDiff.const_smul t hH), jet_smul hH]
    rfl

theorem weighted_variationLowJet {U : Set Base} (hU : IsOpen U)
    {H : Base → Space} (hH : ContDiff ℝ ∞ H) {s C : ℝ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C) (m : ℕ)
    (hb : WeightedBound U s (m + 2) C H) :
    WeightedBound U s m (C / s ^ 2) (variationLowJet H) := by
  apply WeightedBound.pi hU.uniqueDiffOn hs (div_nonneg hC (sq_nonneg s))
    (fun i => (contDiff_pi.mp (variationLowJet_smooth hH) i).contDiffOn)
  intro i
  cases i with
  | inl i =>
    change WeightedBound U s m (C / s ^ 2) (fun _ => (0 : ℝ))
    exact (weightedBound_const U s m (0 : ℝ)).mono_const
      (by simpa only [norm_zero] using div_nonneg hC (sq_nonneg s))
  | inr i =>
    obtain ⟨w, a⟩ := i
    have hlen : (lowWord w).length ≤ 2 := by fin_cases w <;> simp [lowWord]
    have hc := hb.component hU.uniqueDiffOn hs.le hC hH.contDiffOn a
    have hbc : WeightedBound U s (m + ((lowWord w).map coordinateVector).length) C
        (fun p => H p a) := by
      simpa only [List.length_map] using hc.mono_order (Nat.add_le_add_left hlen m)
    have hd := hbc.iteratedDirectional hU hs hC
      (contDiff_pi.mp hH a).contDiffOn ((lowWord w).map coordinateVector)
      (fun v hv => by
        obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
        exact norm_coordinateVector_le j) m
    apply hd.mono_const
    apply div_le_div_of_nonneg_left hC (pow_pos hs 2)
    exact pow_le_pow_of_le_one hs.le hs1 (by simpa only [List.length_map] using hlen)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialAlgebra
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomials in actual coordinate jets, with coefficients smooth in
position, the second jet, and the periodic variable. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial

namespace Expression

lemma smoothCoeffs_map {O : Set LowJet} (e : Expression) (f)
    (hf : ∀ c, ContDiffOn ℝ ∞ c (O ×ˢ Set.univ) → ContDiffOn ℝ ∞ (f c) (O ×ˢ Set.univ))
    (he : e.SmoothCoeffs O) : (e.mapCoeff f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact hf c he
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

lemma smoothCoeffs_mul {O : Set LowJet} {e f : Expression}
    (he : e.SmoothCoeffs O) (hf : f.SmoothCoeffs O) : (e.mul f).SmoothCoeffs O := by
  induction e with
  | coeff c => exact smoothCoeffs_map f _ (fun d hd => he.mul hd) hf
  | atom w a e ih => exact ih he
  | add e g ihe ihg => exact ⟨ihe he.1, ihg he.2⟩

end Expression
end ClosedSurfaceR4.JetPolynomial

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

lemma restore_plane_in_coordinates (i : A.centers) (f : SmallModes.Base → V)
    (hf : tsupport f ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base))
    {x : JetPolynomial.Base} (hx : x ∈ (chart (i : M)).target) :
    restore (i : M) (A.outer i) (f ∘ planeCoordinateIsometry) ((chart (i : M)).symm x) =
      f (planeCoordinateIsometry x) := by
  rw [A.restore_plane_on_source i f hf ((chart (i : M)).map_target hx),(chart (i : M)).right_inv hx]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedAtlasDifferential
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

end SmoothingAtlas
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasFiniteCancellation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite global metric-linear corrections assembled from local phase solvers. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
local instance atlasSolveFiberNormed_ra47d36_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance atlasSolveFiberSpace_ra47d36_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance atlasSolveDualAdd_ra47d36_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance atlasSolveDualSmul_ra47d36_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

local instance atlasSolveSectionNormed_ra47d36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance atlasSolveSectionSpace_ra47d36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_plane (i : A.centers) (F : M → Space) :
    A.jetChartMap i F ∘ planeCoordinateIsometry.symm = spaceCoordinates ∘ A.vectorPlaneRead i F := rfl

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasJetReadBounds
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Weighted bounds for the exact coordinate maps entering the polynomial metric. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem jetPlaneRead_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ τ C : ℝ, 0 < τ → τ ≤ 1 → 0 ≤ C → A.WeightedBound τ m C F →
      WeightedEstimates.WeightedBound univ τ m (D*C)
        (A.jetChartMap i F ∘ planeCoordinateIsometry.symm) := by
  obtain ⟨D,hD,hd⟩ := A.vectorPlaneRead_bound (V := Space) i m
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F hF τ C hτ hτ1 hC hb
  rw [A.jetChartMap_plane]
  have hh := (hd F τ C hτ hτ1 hC hF hb).linear uniqueDiffOn_univ hτ.le
    (A.vectorPlaneRead_smooth i hF).contDiffOn spaceCoordinates.toContinuousLinearMap
  simpa only [mul_assoc,ContinuousLinearEquiv.coe_coe] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LowJetCoordinateChange
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact order-two jet transport under a fixed smooth coordinate map.
The new position is supplied separately, so no inverse coordinate map is
required and the construction applies to arbitrary smooth maps. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology

namespace ClosedSurfaceR4.JetPolynomial

lemma coordinatePartial_smooth {f : Base → ℝ} (hf : ContDiff ℝ ∞ f) (v : Fin 2) :
    ContDiff ℝ ∞ (coordinatePartial f v) :=
  (hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const

lemma coordinateChangeFirst_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (v : Fin 2) (a : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => coordinateChangeFirst T p.1 p.2 v a) := by
  apply ContDiff.sum
  intro i _
  exact ((coordinatePartial_smooth (contDiff_pi.mp hT i) v).comp contDiff_fst).mul
    ((ContinuousLinearMap.proj (.inr (firstJetSlot i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd)

lemma coordinateChangeSecond_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (v w : Fin 2) (a : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => coordinateChangeSecond T p.1 p.2 v w a) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.add
  · apply ContDiff.mul
    · exact (coordinatePartial_smooth (contDiff_pi.mp hT i) w).comp contDiff_fst
    · apply ContDiff.sum
      intro j _
      exact ((coordinatePartial_smooth (contDiff_pi.mp hT j) v).comp contDiff_fst).mul
        ((ContinuousLinearMap.proj (.inr (secondJetSlot j i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
          contDiff_snd)
  · exact ((coordinatePartial_smooth
      (coordinatePartial_smooth (contDiff_pi.mp hT i) w) v).comp contDiff_fst).mul
      ((ContinuousLinearMap.proj (.inr (firstJetSlot i,a)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd)

lemma lowJetCoordinateChange_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T) :
    ContDiff ℝ ∞ (lowJetCoordinateChange T) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i =>
    exact (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).contDiff.comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Base × LowJet → Base))
  | inr i =>
    rcases i with ⟨w,a⟩
    fin_cases w
    · exact (ContinuousLinearMap.proj (.inr (0,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
        (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Base × LowJet → LowJet))
    · exact coordinateChangeFirst_smooth hT 0 a
    · exact coordinateChangeFirst_smooth hT 1 a
    · exact coordinateChangeSecond_smooth hT 0 0 a
    · exact coordinateChangeSecond_smooth hT 0 1 a
    · exact coordinateChangeSecond_smooth hT 1 0 a
    · exact coordinateChangeSecond_smooth hT 1 1 a

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiation preserves finite polynomial dependence on higher jets.
The proof is for actual derivatives, including the low-jet chain rule. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → Expression)
    (hf : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))⟩

lemma smoothCoeffs_lowFactor (O : Set LowJet) (v : Fin 2) (i : LowIndex) :
    (lowFactor v i).SmoothCoeffs O := by
  cases i with
  | inl i => exact contDiffOn_const
  | inr i => exact contDiffOn_const

lemma smoothCoeffs_slow {O : Set LowJet} (hO : IsOpen O) (v : Fin 2)
    {e : Expression} (he : e.SmoothCoeffs O) : (e.slow v).SmoothCoeffs O := by
  induction e with
  | coeff c =>
    apply smoothCoeffs_sumList
    intro i _
    exact smoothCoeffs_mul (smoothCoeffs_lowFactor O v i)
      (LocalPeriodicCalculus.slow_smooth hO he (lowBasis i))
  | atom w a e ih => exact ⟨he, ih he⟩
  | add e f ihe ihf => exact ⟨ihe he.1, ihf he.2⟩

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetPullbackExpressions
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coordinate derivatives in a second chart, expressed by finite jet
polynomials in the first chart. Only the surface and four-space dimensions
used in the primitive construction are considered. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Topology
namespace ClosedSurfaceR4.JetPolynomial

lemma inverseCoordinateCoefficient_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (i k : Fin 2) :
    ContDiff ℝ ∞ (inverseCoordinateCoefficient T S i k) := by
  have hs : ContDiff ℝ ∞ (fun x => (fderiv ℝ S x (coordinateVector i)) k) :=
    contDiff_pi.mp ((hS.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const) k
  exact hs.comp (hT.comp (lowPosition.contDiff.comp contDiff_fst))

lemma jetPullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (w : List (Fin 2)) (a : Fin 4) :
    (jetPullback T S w a).SmoothCoeffs univ := by
  induction w with
  | nil =>
    change ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => z.1 (.inr (0,a))) (univ ×ˢ univ)
    exact ((ContinuousLinearMap.proj (.inr (0,a)) : LowJet →L[ℝ] ℝ).contDiff.comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : LowJet × ℝ → LowJet))).contDiffOn
  | cons i w ih =>
    apply Expression.smoothCoeffs_sumList
    intro k _
    exact Expression.smoothCoeffs_mul (inverseCoordinateCoefficient_smooth hT hS i k).contDiffOn
      (Expression.smoothCoeffs_slow isOpen_univ k ih)


namespace Expression

lemma coordinatePullback_smooth {T S : Base → Base} {K : LowJet → LowJet}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (hK : ContDiff ℝ ∞ K)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.coordinatePullback T S K).SmoothCoeffs univ := by
  induction e with
  | coeff c =>
    have hc : ContDiff ℝ ∞ c := contDiffOn_univ.mp (by simpa only [SmoothCoeffs,univ_prod_univ] using he)
    exact (hc.comp ((hK.comp contDiff_fst).prodMk contDiff_snd)).contDiffOn
  | atom w a e ih => exact smoothCoeffs_mul (jetPullback_smooth hT hS w a) (ih he)
  | add e f ihe ihf => exact ⟨ihe he.1,ihf he.2⟩

end Expression

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinatePolynomialPullback
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The coordinate pullback of a finite jet polynomial, with the low-jet
substitution and inverse differential proved from the actual local inverse.
No compatibility of the polynomial values is assumed. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial

lemma coordinateLowJetSubstitution_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (coordinateLowJetSubstitution T S) :=
  (lowJetCoordinateChange_smooth hS).comp
    ((hT.comp lowPosition.contDiff).prodMk contDiff_id)

namespace Expression

lemma localCoordinatePullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.localCoordinatePullback T S).SmoothCoeffs univ :=
  coordinatePullback_smooth hT hS (coordinateLowJetSubstitution_smooth hT hS) he

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar polynomial representations of the finite metric coefficients. -/
noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.JetPolynomial.Expression
open LocalPeriodicExpansion CovarianceCorrector

lemma smoothCoeffs_sumFinset {ι : Type*} {O : Set LowJet} (a : Finset ι) (e : ι → Expression)
    (he : ∀ i ∈ a, (e i).SmoothCoeffs O) : (sumFinset a e).SmoothCoeffs O := by
  apply smoothCoeffs_sumList
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTensorPullback
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pullback of finite tensor expressions under fixed coordinate changes.
The Jacobian factors, coefficient substitution, and higher jet atoms are
all constructed, so the evaluation identity assumes no tensor covariance. -/
noncomputable section
open Set
open scoped ContDiff BigOperators Matrix Topology

namespace ClosedSurfaceR4.JetPolynomial

lemma tensorCoordinateJacobian_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (k l : Fin 3) : ContDiff ℝ ∞ (tensorCoordinateJacobian T k l) := by
  have hd (v : Base) (a : Fin 2) : ContDiff ℝ ∞ (fun x => fderiv ℝ T x v a) :=
    contDiff_pi.mp ((hT.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const) a
  fin_cases l
  · exact (hd _ 0).mul (hd _ 0)
  · exact ((hd _ 0).mul (hd _ 1)).add ((hd _ 1).mul (hd _ 0))
  · exact (hd _ 1).mul (hd _ 1)

lemma tensorJacobianCoefficient_smooth {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (k l : Fin 3) : ContDiff ℝ ∞ (tensorJacobianCoefficient T k l) :=
  (tensorCoordinateJacobian_smooth hT k l).comp (lowPosition.contDiff.comp contDiff_fst)

namespace TensorExpression

lemma coordinatePullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {E : TensorExpression} (hE : ∀ k, (E k).SmoothCoeffs univ) (k : Fin 3) :
    (coordinatePullback E T S k).SmoothCoeffs univ := by
  apply Expression.smoothCoeffs_sumFinset
  intro l _
  exact Expression.smoothCoeffs_mul (tensorJacobianCoefficient_smooth hT k l).contDiffOn
    (Expression.localCoordinatePullback_smooth hT hS (hE l))

end TensorExpression

namespace Perturbation

lemma tensorPolynomialCoordinatePullback_smooth {n : ℕ}
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {T S : Base → Base} (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    (k : Fin 3) (r : Fin n) :
    (tensorPolynomialCoordinatePullback P T S k r).SmoothCoeffs univ :=
  TensorExpression.coordinatePullback_smooth hT hS (fun l => hP l r) k

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LinearMetricChartReconstruction
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The mixed metric is reconstructed from the genuine chart readings. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
local instance linearReadFiberNormed_ra47d36_1 : NormedAddCommGroup TensorFiber := inferInstance
local instance linearReadFiberSpace_ra47d36_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance linearReadDualAdd_ra47d36_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance linearReadDualSmul_ra47d36_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.linearReadSectionNormed
local instance linearReadSectionSpace_ra47d36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma vectorPlaneRead_add {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : A.centers) (F G : M → V) :
    A.vectorPlaneRead i (F+G) = A.vectorPlaneRead i F + A.vectorPlaneRead i G := by
  funext x
  by_cases hx : planeCoordinateIsometry.symm x ∈ (chart (i : M)).target <;>
    simp [vectorPlaneRead,vectorChartRead,localize,hx,smul_add]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedChartPullback
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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

lemma supportedChartPullback_support (e : OpenPartialHomeomorph Base Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : Base → ℝ} {f : Base → V} {K : Set Base}
    (hK : IsCompact K) (hχ : tsupport χ ⊆ e.source) (hf : tsupport f ⊆ K) :
    tsupport (supportedChartPullback e χ f) ⊆ e.symm '' K := by
  apply closure_minimal _ (hK.image hi.continuous).isClosed
  intro x hx
  have hn : χ x • f (e x) ≠ 0 := hx
  have hc : χ x ≠ 0 := fun hz => hn (by rw [hz,zero_smul])
  have hfx : f (e x) ≠ 0 := fun hz => hn (by rw [hz,smul_zero])
  exact ⟨e x,hf (subset_tsupport f hfx),e.left_inv (hχ (subset_tsupport χ hc))⟩

lemma supportedChartPullback_eq (e : OpenPartialHomeomorph Base Base)
    {χ : Base → ℝ} {f : Base → V} {K : Set Base}
    (hf : tsupport f ⊆ K) (hχ : ∀ x ∈ e.symm '' K, χ x = 1)
    {x : Base} (hx : x ∈ e.source) :
    supportedChartPullback e χ f x = f (e x) := by
  by_cases hz : f (e x) = 0
  · simp only [supportedChartPullback,hz,smul_zero]
  · have hxK : x ∈ e.symm '' K := ⟨e x,hf (subset_tsupport f hz),e.left_inv hx⟩
    simp only [supportedChartPullback,hχ x hxK,one_smul]

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialMetric
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual globally restored polynomial perturbation of the metric,
with its exact first, second and higher-order variation decomposition. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricDualSmul
variable (A : SmoothingAtlas M)
variable {n : A.centers → ℕ}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberSpace
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polynomialMetricFiberNormed
local instance polynomialMetricSectionNormed_ra47d36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialMetricSectionSpace_ra47d36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma jetChartMap_add (i : A.centers) (G X : M → Space) :
    A.jetChartMap i (G+X) = A.jetChartMap i G+A.jetChartMap i X := by
  have h := A.vectorPlaneRead_add i G X
  funext x
  have hh := congrFun h (planeCoordinateIsometry x)
  change spaceCoordinates (A.vectorChartRead i (G+X) x) =
    spaceCoordinates (A.vectorChartRead i G x)+spaceCoordinates (A.vectorChartRead i X x)
  simpa only [vectorPlaneRead,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply,
    Pi.add_apply,map_add] using congrArg spaceCoordinates hh

end SmoothingAtlas
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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactLocalBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform slow-scale bounds on a relatively compact coordinate domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem compact_local_weighted_bound {V Ω K : Set E}
    (hV : IsOpen V) (hΩ : IsOpen Ω) (hK : IsCompact K)
    (hVK : V ⊆ K) (hKΩ : K ⊆ Ω) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f Ω) (m : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ, 0 ≤ s → s ≤ 1 → WeightedBound V s m C f := by
  obtain ⟨C,hC,hb⟩ := compact_coefficient_bound hΩ.uniqueDiffOn hK hKΩ hf m
  refine ⟨C,hC,?_⟩
  intro s hs hs1 j hj x hx
  rw [iteratedFDerivWithin_of_isOpen j hV hx]
  have hh := hb j hj x (hVK hx)
  rw [iteratedFDerivWithin_of_isOpen j hΩ (hKΩ (hVK hx))] at hh
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hs hs1)).trans hh

end ClosedSurfaceR4.WeightedEstimates

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

/-- An unweighted prefix of any lower order is controlled by a shifted bound. -/
lemma ShiftedBound.prefix {q m : ℕ} {s C : ℝ} {f : Base → V}
    (h : ShiftedBound q m s C f) (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    {j : ℕ} (hj : j ≤ q + m) :
    WeightedBound Set.univ 1 j (C / s ^ (j - q)) f := by
  intro i hi x _
  simp only [one_pow, one_mul, iteratedFDerivWithin_univ]
  apply (h.deriv_le hs (hi.trans hj) x).trans
  exact div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le_sub_right hi q))

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_VectorReadPrefixBounds
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Chart readings retain the unweighted derivative prefix of the true map. -/
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

theorem vectorPlaneRead_prefix_bounds (i : A.centers) (q m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → V) (s C : ℝ),
      0 < s → s ≤ 1 → 0 ≤ C → ContMDiff planeModel 𝓘(ℝ,V) ∞ F →
      A.ShiftedBound q m s C F → ∀ j ≤ q+m,
      WeightedEstimates.WeightedBound univ 1 j (D*C/s^(j-q)) (A.vectorPlaneRead i F) := by
  classical
  choose D hD hd using fun j => A.vectorPlaneRead_bound (V := V) i j
  let T := ∑ j ∈ Finset.range (q+m+1), D j
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => hD j)
  refine ⟨T,hT,?_⟩
  intro F s C hs hs1 hC hF hb j hj
  have hp : A.WeightedBound 1 j (C/s^(j-q)) F := fun k => (hb k).prefix hs hs1 hC hj
  have hh := hd j F 1 (C/s^(j-q)) zero_lt_one le_rfl (by positivity) hF hp
  apply hh.mono_const
  calc
    D j*(C/s^(j-q)) = D j*C/s^(j-q) := by ring
    _ ≤ T*C/s^(j-q) := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun k _ => hD k) (Finset.mem_range.mpr (by omega))) hC)
      (pow_nonneg hs.le _)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetPrefixBounds
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bounds on the actual positional two-jet on a fixed bounded domain. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.WeightedEstimates
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem directional_of_prefix {U : Set E} (hU : IsOpen U)
    {f : E → V} (hf : ContDiff ℝ ∞ f) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+1, WeightedBound U 1 j (C/s^(j-1)) f)
    (v : E) (hv : ‖v‖ ≤ 1) :
    WeightedBound U s m C (fun x => fderiv ℝ f x v) := by
  intro j hj x hx
  have hh := ((hb (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn v)
    j le_rfl x hx
  simp only [one_pow,one_mul,div_one,Nat.add_sub_cancel] at hh
  calc
    _ ≤ s^j*(‖v‖*(C/s^j)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
    _ = ‖v‖*C := by field_simp
    _ ≤ C := mul_le_of_le_one_left hC hv

end ClosedSurfaceR4.WeightedEstimates

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem jet_lowWord_bound {U : Set Base} (hU : IsOpen U)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {s C : ℝ} {m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : ∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G)
    (w : Fin 7) (a : Fin 4) :
    WeightedBound U s m C (fun p => jet G (lowWord w) a p) := by
  let f : Base → ℝ := fun p => G p a
  have hf : ContDiff ℝ ∞ f := contDiff_pi.mp hG a
  have hp (j : ℕ) (hj : j ≤ m+2) : WeightedBound U 1 j (C/s^(j-2)) f :=
    (hb j hj).component hU.uniqueDiffOn zero_le_one
      (div_nonneg hC (pow_nonneg hs.le _)) hG.contDiffOn a
  have hzero : WeightedBound U s m C f := by
    intro j hj x hx
    have hh := hp j (by omega) j le_rfl x hx
    simp only [one_pow,one_mul] at hh
    calc
      _ ≤ s^j*(C/s^(j-2)) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ ≤ s^j*(C/s^j) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left hC (pow_pos hs _)
          (pow_le_pow_of_le_one hs.le hs1 (Nat.sub_le _ _))) (pow_nonneg hs.le _)
      _ = C := by field_simp
  have hunit (v : Fin 2) : ‖coordinateVector v‖ = 1 := by
    simp only [coordinateVector,Pi.norm_single,norm_one]
  have hfirst (v : Fin 2) (j : ℕ) (hj : j ≤ m+1) :
      WeightedBound U 1 j (C/s^(j-1)) (fun x => fderiv ℝ f x (coordinateVector v)) := by
    have hh := (hp (j+1) (by omega)).directional hU zero_lt_one hf.contDiffOn (coordinateVector v)
    have he : j+1-2 = j-1 := by omega
    simpa only [hunit,one_mul,div_one,he] using hh
  have hone (v : Fin 2) :
      WeightedBound U s m C (fun x => fderiv ℝ f x (coordinateVector v)) := by
    apply directional_of_prefix hU hf hs hC _ (coordinateVector v) (hunit v).le
    intro j hj
    apply (hp j (by omega)).mono_const
    exact div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 (by omega))
  have htwo (v v' : Fin 2) : WeightedBound U s m C
      (fun x => fderiv ℝ (fun y => fderiv ℝ f y (coordinateVector v')) x (coordinateVector v)) :=
    directional_of_prefix hU
      ((hf.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const)
      hs hC (hfirst v') (coordinateVector v) (hunit v).le
  fin_cases w
  · exact hzero
  · exact hone 0
  · exact hone 1
  · exact htwo 0 0
  · exact htwo 0 1
  · exact htwo 1 0
  · exact htwo 1 1

theorem bounded_lowJet_prefix {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G → ∀ s C : ℝ,
      0 < s → s ≤ 1 → 0 ≤ C →
      (∀ j ≤ m+2, WeightedBound U 1 j (C/s^(j-2)) G) →
      WeightedBound U s m (D+C) (lowJet G) := by
  obtain ⟨D,hD,hd⟩ := compact_local_weighted_bound hU isOpen_univ K.isCompact hUK
    (subset_univ _) (contDiff_id : ContDiff ℝ ∞ (id : Base → Base)).contDiffOn m
  refine ⟨D,hD,?_⟩
  intro G hG s C hs hs1 hC hb
  apply WeightedBound.pi hU.uniqueDiffOn hs (by linarith)
  · intro i
    exact (contDiff_pi.mp (lowJet_smooth hG) i).contDiffOn
  · intro i
    cases i with
    | inl i =>
      exact ((hd s hs.le hs1).component hU.uniqueDiffOn hs.le
        (zero_le_one.trans hD) contDiff_id.contDiffOn i).mono_const (by linarith)
    | inr i =>
      exact (jet_lowWord_bound hU hG hs hs1 hC hb i.1 i.2).mono_const (by linarith)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetCompactRange
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One compact positional-jet range for all maps in a bounded C2 family. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem bounded_lowJet_range {U : Set Base} (hU : IsOpen U)
    (K : Compacts Base) (hUK : U ⊆ K) {C : ℝ} (hC : 0 ≤ C) :
    ∃ Q : Set LowJet, IsCompact Q ∧ ∀ (G : Base → Space), ContDiff ℝ ∞ G →
      WeightedBound U 1 2 C G → MapsTo (lowJet G) U Q := by
  obtain ⟨D,_,hd⟩ := bounded_lowJet_prefix hU K hUK 0
  refine ⟨Metric.closedBall 0 (D+C),isCompact_closedBall _ _,?_⟩
  intro G hG hb p hp
  have hj := hd G hG 1 C zero_lt_one le_rfl hC (fun j hj => by
    simpa only [one_pow,div_one] using hb.mono_order (by omega : j ≤ 2))
  simpa only [Metric.mem_closedBall,dist_zero_right] using hj.norm_le hp

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ShiftedScaleGain
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

/-- Adding the actual increment adds its shifted derivative budget. -/
theorem ShiftedBound.add {q m : ℕ} {s A B : ℝ} {f g : Base → V}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (hs : 0 ≤ s)
    (hb : ShiftedBound q m s A f) (hc : ShiftedBound q m s B g) :
    ShiftedBound q m s (A + B) (f + g) := by
  intro j hj x
  rw [iteratedFDeriv_add_apply (hf.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt
    (hg.of_le (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).contDiffAt]
  calc
    _ ≤ s ^ (j - q) * (‖iteratedFDeriv ℝ j f x‖ + ‖iteratedFDeriv ℝ j g x‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hs _)
    _ = s ^ (j - q) * ‖iteratedFDeriv ℝ j f x‖ +
        s ^ (j - q) * ‖iteratedFDeriv ℝ j g x‖ := by ring
    _ ≤ _ := add_le_add (hb j hj x) (hc j hj x)

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

/-- The new map keeps the old low-derivative baseline; its inherited high
orders contract, and the actual increment contributes its own budget. -/
theorem shifted_map_recurrence {q m : ℕ} {t τ P C D : ℝ} {f u : M → V}
    (hf : ContMDiff planeModel 𝓘(ℝ, V) ∞ f)
    (hu : ContMDiff planeModel 𝓘(ℝ, V) ∞ u)
    (hb : A.ShiftedBound q 0 t P f) (hc : A.ShiftedBound q m t C f)
    (hd : A.ShiftedBound q m τ D u)
    (ht : 0 < t) (hτ : 0 ≤ τ) (hτt : τ ≤ t) (hP : 0 ≤ P) (hC : 0 ≤ C) :
    A.ShiftedBound q m τ (P + (τ / t) * C + D) (f + u) := by
  have hsh := A.shifted_shrink_with_prefix hb hc ht hτ hτt hP hC
  intro i
  rw [localize_add]
  exact (hsh i).add
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hf)
    (localize_smooth (i : M) (A.weight_smooth i) (A.weight_support i) hu) hτ (hd i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_GlobalInputRecurrence
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma shiftedBound_of_weighted {f : Base → V} {s C : ℝ} {q m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : WeightedEstimates.WeightedBound univ s (q+m) C f) :
    ShiftedBound q m s (C/s^q) f := by
  intro j hj x
  have hh := hb.deriv_le hs hj (mem_univ x)
  rw [iteratedFDerivWithin_univ] at hh
  by_cases hq : q ≤ j
  · have he : s^j = s^(j-q)*s^q := by rw [← pow_add,Nat.sub_add_cancel hq]
    calc
      _ ≤ s^(j-q)*(C/s^j) := mul_le_mul_of_nonneg_left hh (pow_nonneg hs.le _)
      _ = _ := by rw [he]; field_simp
  · have hjq : j ≤ q := by omega
    simp only [Nat.sub_eq_zero_of_le hjq,pow_zero,one_mul]
    exact hh.trans (div_le_div_of_nonneg_left hC (pow_pos hs _)
      (pow_le_pow_of_le_one hs.le hs1 hjq))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.inputRecurrenceFiberSpace
omit [CompactSpace M] in
lemma weighted_to_shifted {F : M → V} {s C : ℝ} {q m : ℕ}
    (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hb : A.WeightedBound s (q+m) C F) : A.ShiftedBound q m s (C/s^q) F :=
  fun i => shiftedBound_of_weighted hs hs1 hC (hb i)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasRestoredPolynomialDirection
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A supported Euclidean field is restored with exactly its original
localized jet, so the local polynomial solver acts on the actual direction. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberSpace
local instance restoredDirectionDualSmul_ra47d36_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.restoredDirectionFiberNormed
local instance restoredDirectionSectionNormed_ra47d36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance restoredDirectionSectionSpace_ra47d36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma jetChartMap_restored_direction (i : A.centers) (X : RealModes.RField 4)
    (hX : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    A.jetChartMap i (restore (i : M) (A.outer i)
      ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) = X ∘ planeCoordinateIsometry := by
  have hsp := (tsupport_comp_subset (g := spaceCoordinates.symm) (map_zero _) X).trans hX
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · change spaceCoordinates (localize (i : M) (A.outer i)
      (restore (i : M) (A.outer i) ((spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry)) x) = _
    rw [localize,indicator_of_mem hx,A.restore_plane_in_coordinates i _ hsp hx]
    simp only [Function.comp_apply,map_smul,ContinuousLinearEquiv.apply_symm_apply]
    by_cases hz : X (planeCoordinateIsometry x) = 0
    · rw [hz,smul_zero]
    · have hp : (chart (i : M)).symm x ∈ tsupport (A.weight i) := by
        apply A.mem_weight_support_of_plane i ((chart (i : M)).map_target hx)
        rw [(chart (i : M)).right_inv hx]
        exact hX (subset_tsupport X hz)
      rw [A.outer_one i _ hp,one_pow,one_smul]
  · have hz : X (planeCoordinateIsometry x) = 0 := by
      by_contra hn
      obtain ⟨y,hy,he⟩ := hX (subset_tsupport X hn)
      have hyx : y = x := planeCoordinateIsometry.injective he
      subst y
      obtain ⟨p,hp,rfl⟩ := hy
      exact hx ((chart (i : M)).map_source (A.weight_support i hp))
    change spaceCoordinates (localize (i : M) (A.outer i) _ x) = _
    rw [localize,indicator_of_notMem hx,map_zero]
    exact hz.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasPeriodicAnsatz
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The supported finite periodic ansatz is a genuine global smooth map,
with exactly the intended coordinate jets on its chosen chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma jetChartMap_restored_supported (i : A.centers) (H : JetPolynomial.Base → Space)
    (hH : tsupport H ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.jetChartMap i (restore (i : M) (A.outer i) H) = spaceCoordinates ∘ H := by
  let X : RealModes.RField 4 := spaceCoordinates ∘ H ∘ planeCoordinateIsometry.symm
  have hx : tsupport X ⊆ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    have hs := tsupport_comp_subset (g := spaceCoordinates) (map_zero _)
      (H ∘ planeCoordinateIsometry.symm)
    have ht := tsupport_comp_preimage H planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous
    intro x hxx
    have hh := hH (ht (hs hxx))
    exact ⟨planeCoordinateIsometry.symm x,hh,planeCoordinateIsometry.apply_symm_apply x⟩
  have he : (spaceCoordinates.symm ∘ X) ∘ planeCoordinateIsometry = H := by
    funext x
    simp [X]
  have hh := A.jetChartMap_restored_direction i X hx
  rw [he] at hh
  funext x
  simpa only [X,Function.comp_apply,planeCoordinateIsometry.symm_apply_apply] using congrFun hh x

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasAnsatz
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

omit [CompactSpace M] in
lemma phaseAtlasLocalIncrement_support (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    tsupport (A.phaseAtlasLocalIncrement i F e χ U ℓ L z) ⊆ e.symm '' K :=
  supportedChartPullback_support e hi hK hχ
    (finiteAnsatz_tsupport_sub _ U hK.isClosed hzero ℓ L z)

lemma phaseAtlasAnsatz_coordinate (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hχone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) {x : JetPolynomial.Base} (hx : x ∈ e.source) :
    A.jetChartMap i (A.phaseAtlasAnsatz i F e χ U ℓ L z) x =
      spaceCoordinates (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z (e x)) := by
  have hs := (A.phaseAtlasLocalIncrement_support i F e hi hχ U hK hzero ℓ L z).trans hKA
  have heq := A.jetChartMap_restored_supported i (A.phaseAtlasLocalIncrement i F e χ U ℓ L z) hs
  rw [phaseAtlasAnsatz,A.jetChartMap_add,heq]
  change spaceCoordinates (A.vectorChartRead i F x) +
    spaceCoordinates (supportedChartPullback e χ
      (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z -
        (A.vectorChartRead i F ∘ e.symm)) x) = _
  have hpull := supportedChartPullback_eq e
    (f := finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z - (A.vectorChartRead i F ∘ e.symm))
    (show tsupport (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z - (A.vectorChartRead i F ∘ e.symm)) ⊆ K from
      finiteAnsatz_tsupport_sub _ U hK.isClosed hzero ℓ L z) hχone hx
  rw [hpull]
  simp only [Pi.sub_apply,Function.comp_apply,e.left_inv hx,map_sub]
  abel

lemma phaseAtlasAnsatz_eventuallyEq (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : M} (hp : p ∉ tsupport (A.weight i)) :
    A.phaseAtlasAnsatz i F e χ U ℓ L z =ᶠ[𝓝 p] F := by
  let H := A.phaseAtlasLocalIncrement i F e χ U ℓ L z
  have hs : tsupport H ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base) :=
    (A.phaseAtlasLocalIncrement_support i F e hi hχ U hK hzero ℓ L z).trans hKA
  have hs' : tsupport (H ∘ planeCoordinateIsometry.symm) ⊆
      (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) := by
    intro x hx
    have hh := hs (tsupport_comp_preimage H planeCoordinateIsometry.symm planeCoordinateIsometry.symm.continuous hx)
    exact ⟨planeCoordinateIsometry.symm x,hh,planeCoordinateIsometry.apply_symm_apply x⟩
  have heq : (H ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry = H := by
    funext x
    simp
  have ht := A.restore_plane_tsupport i (H ∘ planeCoordinateIsometry.symm) hs'
  rw [heq] at ht
  have hz := notMem_tsupport_iff_eventuallyEq.mp (fun h => hp (ht h))
  filter_upwards [hz] with x hx
  change F x + restore (i : M) (A.outer i) H x = F x
  rw [hx]
  exact add_zero _

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_PhaseAnsatzNormal
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the actual second jet of a supported phase-chart ansatz on the
inverse chart; this transfers the quantitative normal profile unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates

lemma primitiveNormalTriple_germ {f g : Base → Euclidean} {p : Base}
    (h : f =ᶠ[𝓝 p] g) : primitiveNormalTriple f p = primitiveNormalTriple g p := by
  have hd : (fun q => fderiv ℝ f q (coordinateVector 1)) =ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (coordinateVector 1)) :=
    h.fderiv.mono (fun _ hh => congrArg (fun L : Base →L[ℝ] Euclidean => L (coordinateVector 1)) hh)
  ext k a
  fin_cases k <;> simp only [primitiveNormalTriple,h.fderiv_eq,hd.fderiv_eq]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial LocalPeriodicExpansion CovarianceCorrector SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseAtlasAnsatz_inverse_germ (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : JetPolynomial.Base} (hp : p ∈ e.target) :
    A.vectorChartRead i (A.phaseAtlasAnsatz i F e χ U ℓ L z) ∘ e.symm =ᶠ[𝓝 p]
      finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z := by
  filter_upwards [e.open_target.mem_nhds hp] with y hy
  have hh := A.phaseAtlasAnsatz_coordinate i F e hi hχ U hK hKA hzero hone ℓ L z (e.map_target hy)
  apply spaceCoordinates.injective
  simpa only [jetChartMap,Function.comp_apply,e.right_inv hy] using hh

lemma phaseAtlasAnsatz_normalTriple (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : JetPolynomial.Base} (hp : p ∈ e.target) :
    primitiveNormalTriple (A.vectorChartRead i (A.phaseAtlasAnsatz i F e χ U ℓ L z) ∘ e.symm) p =
      primitiveNormalTriple (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z) p :=
  primitiveNormalTriple_germ
    (A.phaseAtlasAnsatz_inverse_germ i F e hi hχ U hK hKA hzero hone ℓ L z hp)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPrimitivePolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Embed the three mean-polynomial coefficients of one primitive in the
actual global atlas operator, with zero contribution from every other chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyFiberSpace
local instance primitivePolyDualSmul_ra47d36_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.primitivePolyFiberNormed
local instance primitivePolySectionNormed_ra47d36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance primitivePolySectionSpace_ra47d36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma primitiveAtlasPolynomial_smooth {n : ℕ} (i : A.centers)
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ) :
    ∀ j k r, (A.primitiveAtlasPolynomial i P j k r).SmoothCoeffs univ := by
  classical
  intro j k r
  by_cases hji : j = i
  · simpa only [primitiveAtlasPolynomial,ite_eq_left hji] using hP k r
  · simp only [primitiveAtlasPolynomial,ite_eq_right hji,Expression.SmoothCoeffs]
    exact contDiffOn_const

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CutoffTensorPolynomial
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Positional cutoffs of the actual finite tensor polynomial. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial.Perturbation

lemma cutoffTensorPolynomial_smooth {n : ℕ} {χ : Base → ℝ}
    (hχ : ContDiff ℝ ∞ χ) {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k r, (P k r).SmoothCoeffs univ) (k : Fin 3) (r : Fin n) :
    (cutoffTensorPolynomial χ P k r).SmoothCoeffs univ :=
  Expression.smoothCoeffs_mul
    ((hχ.comp (lowPosition.contDiff.comp contDiff_fst)).contDiffOn) (hP k r)

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetSegment
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact low-jet margins and uniform bounds along the actual Taylor
segment, obtained from the second derivatives of the displacement. -/
noncomputable section
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_segment_dist {U : Set Base} (hU : IsOpen U)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {s C : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hHb : WeightedBound U s 2 C H) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    {p : Base} (hp : p ∈ U) :
    dist (lowJet (fun q => G q + t • H q) p) (lowJet G p) ≤ C / s ^ 2 := by
  have hv := weighted_variationLowJet hU hH hs hs1 hC 0 hHb
  rw [lowJet_affine hG hH t p, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  exact (mul_le_of_le_one_left (norm_nonneg _) ht1).trans (hv.norm_le hp)

theorem exists_lowJet_segment_margin {Q O : Set LowJet}
    (hQ : IsCompact Q) (hO : IsOpen O) (hQO : Q ⊆ O) :
    ∃ (ρ : ℝ) (Q' : Set LowJet), 0 < ρ ∧ IsCompact Q' ∧ Q ⊆ Q' ∧ Q' ⊆ O ∧
      ∀ {U : Set Base}, IsOpen U → ∀ {G H : Base → Space},
      ContDiff ℝ ∞ G → ContDiff ℝ ∞ H → Set.MapsTo (lowJet G) U Q →
      ∀ {s C : ℝ}, 0 < s → s ≤ 1 → 0 ≤ C → C / s ^ 2 ≤ ρ →
      WeightedBound U s 2 C H → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Set.MapsTo (lowJet (fun p => G p + t • H p)) U Q' := by
  obtain ⟨ρ,hρ,hsub⟩ := hQ.exists_cthickening_subset_open hO hQO
  refine ⟨ρ,Metric.cthickening ρ Q,hρ,hQ.cthickening,Metric.self_subset_cthickening Q,hsub,?_⟩
  intro U hU G H hG hH hGQ s C hs hs1 hC hsmall hHb t ht p hp
  exact Metric.mem_cthickening_of_dist_le _ (lowJet G p) ρ Q (hGQ hp)
    ((lowJet_segment_dist hU hG hH hs hs1 hC hHb ht hp).trans hsmall)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMeanApproximation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite slow iteration solves the actual restored polynomial mean
metric to any prescribed finite unweighted order. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PrimitiveRealization WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxFiberSpace
local instance meanApproxDualAdd_ra47d36_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.meanApproxFiberNormed
local instance meanApproxSectionNormed_ra47d36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance meanApproxSectionSpace_ra47d36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorWeightedBound_unscaled {H : ∀ x : M, CovariantTwoTensor x}
    {s C : ℝ} {m : ℕ} (hs : 0 < s) (hs1 : s ≤ 1) (hC : 0 ≤ C)
    (hH : A.TensorWeightedBound s m C H) : A.TensorWeightedBound 1 m (C/s^m) H := by
  intro i j hj x hx
  simp only [one_pow,one_mul]
  exact ((hH i).deriv_le hs hj hx).trans (div_le_div_of_nonneg_left hC (pow_pos hs _)
    (pow_le_pow_of_le_one hs.le hs1 hj))

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactCompositionPrefix
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth changes of coordinates preserve the second-order
rescaled derivative profile needed by the primitive recursion. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

theorem compact_composition_prefix {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {S : Set Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : Base → Space) (s C : ℝ),
      0 < s → 0 ≤ C → ContDiff ℝ ∞ f →
      (∀ j, j ≤ m+2 → WeightedBound univ 1 j (C/s^(j-2)) f) →
      ∀ j, j ≤ m+2 → WeightedBound S 1 j (D*C/s^(j-2)) (f ∘ T) := by
  obtain ⟨B,hB,hTb⟩ := compact_local_weighted_bound hS isOpen_univ hSc
    subset_closure (subset_univ _) hT.contDiffOn (m+2)
  let D : ℝ := ((m+2).factorial : ℝ)*B^(m+2)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.factorial_pos (m+2)) (one_le_pow₀ hB)
  refine ⟨D,hD,?_⟩
  intro f s C hs hC hf hb j hj
  have hcoord : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ k T S x‖ ≤ B := by
    intro k _ hk x hx
    simpa only [one_pow,one_mul] using hTb 1 zero_le_one le_rfl k (hk.trans hj) x hx
  have hh := (hb j hj).comp_coordinates hS.uniqueDiffOn uniqueDiffOn_univ zero_lt_one le_rfl
    hB (div_nonneg hC (pow_nonneg hs.le _)) hT.contDiffOn hf.contDiffOn
    (fun _ _ => mem_univ _) hcoord
  have hc : (j.factorial : ℝ)*B^j ≤ D := mul_le_mul
    (by exact_mod_cast Nat.factorial_le hj)
    (pow_le_pow_right₀ hB hj) (by positivity) (by positivity)
  apply hh.mono_const
  calc
    (j.factorial : ℝ)*(C/s^(j-2))*B^j = ((j.factorial : ℝ)*B^j)*(C/s^(j-2)) := by ring
    _ ≤ D*(C/s^(j-2)) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = D*C/s^(j-2) := by ring

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_NonlinearLowJetNeighborhood
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed compact admissible neighborhood for the primitive's slow maps,
obtained from the global C2 displacement estimate. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem nonlinear_lowJet_neighborhood_of_C2 (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {S : Set JetPolynomial.Base} (hS : IsOpen S) (hSc : IsCompact (closure S))
    {Q O : Set LowJet} (hQ : IsCompact Q) (hO : IsOpen O) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A.jetChartMap i F ∘ T)) S Q) :
    ∃ (ρ : ℝ) (Q' : Set LowJet), 0 < ρ ∧ IsCompact Q' ∧ Q' ⊆ O ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
        A.WeightedBound 1 2 ρ (G-F) → MapsTo (lowJet (A.jetChartMap i G ∘ T)) S Q' := by
  obtain ⟨r,Q',hr,hQ',_,hQ'O,hnear⟩ := exists_lowJet_segment_margin hQ hO hQO
  obtain ⟨Dr,hDr,hd⟩ := A.jetPlaneRead_bound i 2
  obtain ⟨Dc,hDc,hc⟩ := compact_composition_prefix hT hS hSc 0
  let ρ := r/(1+Dc*Dr)
  have hDc0 : 0 ≤ Dc := zero_le_one.trans hDc
  have hρ : 0 < ρ := div_pos hr (by positivity)
  refine ⟨ρ,Q',hρ,hQ',hQ'O,?_⟩
  intro G hG hclose
  have hdiff := hd (G-F) (hG.sub hF) 1 ρ zero_lt_one le_rfl hρ.le hclose
  have hglobal := weightedBound_comp_isometry planeCoordinateIsometry
    ((A.jetChartMap_smooth i (hG.sub hF)).comp planeCoordinateIsometry.symm.contDiff) hdiff
  have heq : (A.jetChartMap i (G-F) ∘ planeCoordinateIsometry.symm) ∘
      planeCoordinateIsometry = A.jetChartMap i (G-F) := by funext x; simp
  change WeightedEstimates.WeightedBound univ 1 2 (Dr*ρ)
    ((A.jetChartMap i (G-F) ∘ planeCoordinateIsometry.symm) ∘ planeCoordinateIsometry) at hglobal
  rw [heq] at hglobal
  have hcomp := hc (A.jetChartMap i (G-F)) 1 (Dr*ρ) zero_lt_one (by positivity)
    (A.jetChartMap_smooth i (hG.sub hF)) (fun j hj => by
      simpa only [one_pow,div_one] using hglobal.mono_order (by omega : j ≤ 2)) 2 (by omega)
  have hsmall : Dc*(Dr*ρ)/1^2 ≤ r := by
    simp only [one_pow,div_one]
    calc
      Dc*(Dr*ρ) ≤ (1+Dc*Dr)*ρ := by nlinarith [hρ.le]
      _ = r := by dsimp [ρ]; field_simp
  have hh := hnear hS ((A.jetChartMap_smooth i hF).comp hT)
    ((A.jetChartMap_smooth i (hG.sub hF)).comp hT) hFQ zero_lt_one le_rfl
    (show 0 ≤ Dc*(Dr*ρ) by positivity) hsmall
    (by simpa only [one_pow,div_one,Pi.sub_def] using hcomp) 1 ⟨by norm_num,le_rfl⟩
  have hsum : (fun p => (A.jetChartMap i F ∘ T) p+
      (1 : ℝ) • (A.jetChartMap i (G-F) ∘ T) p) = A.jetChartMap i G ∘ T := by
    have had := A.jetChartMap_add i F (G-F)
    have hfg : F+(G-F) = G := by abel
    rw [hfg] at had
    funext p
    simpa only [one_smul,Pi.add_apply,Function.comp_apply] using congrFun had.symm (T p)
  change MapsTo (lowJet (fun p => (A.jetChartMap i F ∘ T) p+
    (1 : ℝ) • (A.jetChartMap i (G-F) ∘ T) p)) S Q' at hh
  rw [hsum] at hh
  exact hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveMetricPowers
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The fast remainder stays arbitrarily small at a prescribed unweighted
order when the slow exponent is chosen after its fixed loss. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

lemma primitive_tail_power_bound {z b : ℝ} {N R loss : ℕ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hb : 0 ≤ b) (hbl : b < 1/(1+(loss : ℝ))) :
    z^(N+R+1)/(z^b)^loss/z^R ≤ z^N := by
  have hl : 0 ≤ (loss : ℝ) := Nat.cast_nonneg _
  have hbl' : b*(1+(loss : ℝ)) < 1 := (lt_div_iff₀ (by positivity)).mp hbl
  have he : (N : ℝ) ≤ (N+R+1 : ℕ)-b*(loss : ℝ)-(R : ℝ) := by
    push_cast
    nlinarith
  have hid : z^(N+R+1)/(z^b)^loss/z^R =
      z^((N+R+1 : ℕ)-b*(loss : ℝ)-(R : ℝ)) := by
    rw [← Real.rpow_natCast z (N+R+1),← Real.rpow_mul_natCast hz.le,
      ← Real.rpow_natCast z R,← Real.rpow_sub hz,← Real.rpow_sub hz]
  rw [hid]
  simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_ge hz hz1 he

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveShiftedPowers
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chosen slow scale also gives the finite two-jet input budget for
the actual periodic primitive. -/
noncomputable section
namespace ClosedSurfaceR4.PrimitiveRealization

lemma slow_power_dominates_fast {z b : ℝ} {loss : ℕ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hb : 0 ≤ b) (hbl : b < 1/(1+(loss : ℝ))) :
    z ≤ (z^b)^loss := by
  have hbl' : b*(1+(loss : ℝ)) < 1 := (lt_div_iff₀ (by positivity)).mp hbl
  have hpow : b*(loss : ℝ) ≤ 1 := by nlinarith
  rw [← Real.rpow_mul_natCast hz.le]
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hz hz1 hpow

lemma primitive_shifted_budget {z s P Q D : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hzs : z ≤ s)
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (_hD : 0 ≤ D) :
    P+(z/s)*Q+D/z^2 ≤ (P+Q+D)/z^2 := by
  have hs : 0 < s := hz.trans_le hzs
  have hratio : z/s ≤ 1 := (div_le_one hs).mpr hzs
  have hbase : P+(z/s)*Q ≤ P+Q := by
    exact add_le_add le_rfl (mul_le_of_le_one_left hQ hratio)
  have hbase0 : 0 ≤ P+(z/s)*Q := add_nonneg hP (mul_nonneg (div_nonneg hz.le hs.le) hQ)
  have hzsq : z^2 ≤ 1 := by nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hz)).mpr
  calc
    (P+(z/s)*Q+D/z^2)*z^2 = (P+(z/s)*Q)*z^2+D := by field_simp
    _ ≤ P+(z/s)*Q+D := add_le_add (mul_le_of_le_one_right hbase0 hzsq) le_rfl
    _ ≤ P+Q+D := add_le_add hbase le_rfl

lemma primitive_normal_threshold {b ε : ℝ} {loss : ℕ} (hb : 0 ≤ b)
    (hbl : b < 1/(1+(loss : ℝ))) (hε : 0 < ε) (D : ℝ) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧ ∀ z : ℝ, 0 < z → z < η →
      D*z/(z^b)^loss < ε := by
  have hbl' : b*(1+(loss : ℝ)) < 1 := (lt_div_iff₀ (by positivity)).mp hbl
  have he : 0 < 1-b*(loss : ℝ) := by nlinarith
  obtain ⟨η,hη,hη1,hh⟩ := ExactCorrection.positive_power_threshold D (1-b*(loss : ℝ)) ε he hε
  refine ⟨η,hη,hη1,?_⟩
  intro z hz hzη
  have hid : D*z/(z^b)^loss = D*z^(1-b*(loss : ℝ)) := by
    rw [← Real.rpow_mul_natCast hz.le,Real.rpow_sub hz,Real.rpow_one,mul_div_assoc]
  rw [hid]
  exact hh z hz hzη

end ClosedSurfaceR4.PrimitiveRealization

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveWeightedBudget
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A slow two-jet profile gives a uniform fast weighted budget, including
the low derivatives that are obscured by the shifted budget alone. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial
variable {M V : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma weighted_of_shifted_two {F : M → V} {z s C : ℝ} {m : ℕ}
    (hz : 0 ≤ z) (hzs : z ≤ s) (hs1 : s ≤ 1)
    (hb : A.ShiftedBound 2 m s C F) : A.WeightedBound z m C F := by
  intro i j hj x _
  rw [iteratedFDerivWithin_univ]
  have hp : z^j ≤ s^(j-2) :=
    (pow_le_pow_left₀ hz hzs j).trans
      (pow_le_pow_of_le_one (hz.trans hzs) hs1 (Nat.sub_le j 2))
  exact (mul_le_mul_of_nonneg_right hp (norm_nonneg _)).trans
    (hb i j (by omega) x)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_NonlinearJetProfiles
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual slow-map jet bounds in a fixed nonlinear phase chart. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem nonlinear_jet_profiles (i : A.centers) {T : JetPolynomial.Base → JetPolynomial.Base}
    (hT : ContDiff ℝ ∞ T) {S : Set JetPolynomial.Base} (hS : IsOpen S)
    (hSc : IsCompact (closure S)) (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) :
    ∃ (Q : Set LowJet) (B : ℕ → ℝ), IsCompact Q ∧ (∀ m, 1 ≤ B m) ∧
      ∀ (G : M → Space), ContMDiff planeModel spaceModel ∞ G →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ m, A.ShiftedBound 2 m s (R m) G) →
      MapsTo (lowJet (A.jetChartMap i G ∘ T)) S Q ∧
      ∀ m, WeightedEstimates.WeightedBound S s m (B m) (lowJet (A.jetChartMap i G ∘ T)) := by
  choose E hE he using fun m => A.vectorPlaneRead_prefix_bounds (V := Space) i 2 m
  choose D hD hd using fun m => compact_composition_prefix hT hS hSc m
  let C := fun m => D m * (‖spaceCoordinates.toContinuousLinearMap‖ * E m * R m)
  have hC (m) : 0 ≤ C m := mul_nonneg (zero_le_one.trans (hD m))
    (mul_nonneg (mul_nonneg (norm_nonneg _) (hE m)) (hR m))
  have hpref (G : M → Space) (hG : ContMDiff planeModel spaceModel ∞ G)
      (s : ℝ≥0) (hs : 0 < (s : ℝ)) (hs1 : s ≤ 1)
      (hb : ∀ m, A.ShiftedBound 2 m s (R m) G) (m j) (hj : j ≤ m+2) :
      WeightedEstimates.WeightedBound S 1 j (C m/(s:ℝ)^(j-2)) (A.jetChartMap i G ∘ T) := by
    apply hd m (A.jetChartMap i G) s (‖spaceCoordinates.toContinuousLinearMap‖ * E m * R m)
      hs (mul_nonneg (mul_nonneg (norm_nonneg _) (hE m)) (hR m))
      (A.jetChartMap_smooth i hG) ?_ j hj
    intro k hk
    have hh := (he m G s (R m) hs hs1 (hR m) hG (hb m) k (by omega)).linear
      uniqueDiffOn_univ zero_le_one (A.vectorPlaneRead_smooth i hG).contDiffOn
      spaceCoordinates.toContinuousLinearMap
    have hc := weightedBound_comp_isometry planeCoordinateIsometry
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hG)) hh
    have heq : (spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry =
        A.jetChartMap i G := by
      funext x
      have hx := congrFun (A.jetChartMap_plane i G) (planeCoordinateIsometry x)
      simpa only [Function.comp_apply,LinearIsometryEquiv.symm_apply_apply] using hx.symm
    change WeightedEstimates.WeightedBound univ 1 k _
      ((spaceCoordinates ∘ A.vectorPlaneRead i G) ∘ planeCoordinateIsometry) at hc
    rw [heq] at hc
    simpa only [mul_div_assoc,mul_assoc] using hc
  let K : TopologicalSpace.Compacts JetPolynomial.Base := ⟨closure S,hSc⟩
  obtain ⟨Q,hQ,hmaps⟩ := bounded_lowJet_range hS K subset_closure (hC 0)
  choose J hJ hj using fun m => bounded_lowJet_prefix hS K subset_closure m
  refine ⟨Q,fun m => J m+C m,hQ,fun m => (hJ m).trans (le_add_of_nonneg_right (hC m)),?_⟩
  intro G hG s hs hs1 hb
  refine ⟨?_,fun m => hj m _ ((A.jetChartMap_smooth i hG).comp hT) s (C m) hs hs1 (hC m)
    (hpref G hG s hs hs1 hb m)⟩
  apply hmaps _ ((A.jetChartMap_smooth i hG).comp hT)
  simpa only [Nat.sub_self,pow_zero,div_one] using hpref G hG s hs hs1 hb 0 2 (by omega)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseAnsatzProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Retain the actual second jet of a supported phase-chart ansatz on the
inverse chart; this transfers the quantitative normal profile unchanged. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates

lemma primitiveJetProfile_germ {f g : Base → Euclidean} {p : Base}
    (h : f =ᶠ[𝓝 p] g) (z : ℝ) : primitiveJetProfile f z p = primitiveJetProfile g z p := by
  have hd (v : Base) : PeriodicExpansion.directionalMap f v =ᶠ[𝓝 p]
      PeriodicExpansion.directionalMap g v :=
    h.fderiv.mono (fun _ hh => congrArg (fun L : Base →L[ℝ] Euclidean => L v) hh)
  ext k a
  fin_cases k <;> simp only [primitiveJetProfile,
    PeriodicExpansion.directionalMap,h.fderiv_eq,(hd (coordinateVector 0)).fderiv_eq,
    (hd (coordinateVector 1)).fderiv_eq]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial LocalPeriodicExpansion CovarianceCorrector SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseAtlasAnsatz_jetProfile (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : JetPolynomial.Base} (hp : p ∈ e.target) :
    primitiveJetProfile (A.vectorChartRead i (A.phaseAtlasAnsatz i F e χ U ℓ L z) ∘ e.symm) z p =
      primitiveJetProfile (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z) z p :=
  primitiveJetProfile_germ
    (A.phaseAtlasAnsatz_inverse_germ i F e hi hχ U hK hKA hzero hone ℓ L z hp) z

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhasePrimitiveSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Preserve the actual primitive support instead of enlarging it to the
whole atlas patch. The closure also works without a Hausdorff hypothesis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseAtlasAnsatz_tsupport_sub (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ) :
    tsupport (A.phaseAtlasAnsatz i F e χ U ℓ L z-F) ⊆ A.phaseSurfaceSupport i e K := by
  let H := A.phaseAtlasLocalIncrement i F e χ U ℓ L z
  have he : A.phaseAtlasAnsatz i F e χ U ℓ L z-F = restore (i : M) (A.outer i) H := by
    funext p
    change F p+restore (i : M) (A.outer i) H p-F p = _
    abel
  rw [he]
  apply closure_minimal _ isClosed_closure
  intro p hp
  by_cases hs : p ∈ (chart (i : M)).source
  · have hn : H (chart (i : M) p) ≠ 0 := by
      intro hz
      apply hp
      simp only [restore,indicator_of_mem hs,hz,smul_zero]
    have hmem := A.phaseAtlasLocalIncrement_support i F e hi hχ U hK hzero ℓ L z
      (subset_tsupport H hn)
    apply subset_closure
    exact ⟨chart (i : M) p,hmem,(chart (i : M)).left_inv hs⟩
  · exact False.elim (hp (by simp only [restore,indicator_of_notMem hs]))

omit [CompactSpace M] in
lemma phaseAtlasAnsatz_eventuallyEq_precise (i : A.centers) (F : M → Space)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (hi : ContDiff ℝ ∞ e.symm) {χ : JetPolynomial.Base → ℝ} (hχ : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K)
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {p : M} (hp : p ∉ A.phaseSurfaceSupport i e K) :
    A.phaseAtlasAnsatz i F e χ U ℓ L z =ᶠ[𝓝 p] F := by
  have hz := notMem_tsupport_iff_eventuallyEq.mp
    (fun h => hp (A.phaseAtlasAnsatz_tsupport_sub i F e hi hχ U hK hzero ℓ L z h))
  filter_upwards [hz] with q hq
  change A.phaseAtlasAnsatz i F e χ U ℓ L z q-F q = 0 at hq
  exact sub_eq_zero.mp hq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentProfiledPhase
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Construct the actual globally supported primitive from the finite recursion
and its extended polynomial mean operator. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation LocalPeriodicExpansion CovarianceCorrector WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
open PrimitiveRealization
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseFiberSpace
local instance independentProfiledPhaseDualSmul_ra47d36_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentProfiledPhaseFiberNormed
local instance independentProfiledPhaseSectionNormed_ra47d36_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independentProfiledPhaseSectionSpace_ra47d36_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Arbitrary finite metric accuracy for the actual supported primitive
in a fixed nonlinear phase chart, using only the proved polynomial mean iteration. -/
theorem independent_profiled_phase_primitive_realization_oai (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : JetPolynomial.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude a)
    (S : TopologicalSpace.Opens JetPolynomial.Base)
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base))) (hTS : MapsTo e e.source S)
    {Q : Set LowJet} (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (hFQ : MapsTo (lowJet (A₀.jetChartMap i F ∘ e.symm)) S Q)
    (K : Set JetPolynomial.Base) (hK : IsCompact K) (hKS : K ⊆ S)
    (hKA : e.symm '' K ⊆ (A₀.chartWeightCompact i : Set JetPolynomial.Base))
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (hv : ∀ J ∈ O, lowJetPosition J ∉ K → ∀ t, l.velocity (J,t) = SurfaceVelocityFamily.normal J)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector 0) = 1) (hℓy : ℓ (coordinateVector 1) = 0)
    :
    ∃ c cB V₀ : ℝ, 0 < c ∧ 0 < cB ∧ 0 ≤ V₀ ∧ ∀ R N : ℕ,
    ∃ lp : ℕ, ∃ (b u η L C Cv Dp : ℝ) (P : ℕ → ℝ), 0 ≤ b ∧ b < 1/16 ∧ 0 < u ∧
      0 < η ∧ η ≤ 1 ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 ≤ Cv ∧ 0 ≤ Dp ∧
      b < 1/(1+(lp : ℝ)) ∧ (∀ m, 0 ≤ P m) ∧
      ∀ z : ℝ, 0 < z → z < η → ∃ G V : M → Space,
        ContMDiff planeModel spaceModel ∞ G ∧ ContMDiff planeModel spaceModel ∞ V ∧
        A₀.WeightedBound 1 3 (L*z^u) (G-F) ∧
        (∀ m, A₀.ShiftedBound 2 m (z^b) (P m) G) ∧
        A₀.WeightedBound z R Cv V ∧
        A₀.WeightedBound 1 0 V₀ V ∧
        A₀.ShiftedBound 2 R z (Cv/z^2) V ∧
        A₀.TensorWeightedBound 1 R (C*z^N)
          (inducedTensor V-(g.inner+A₀.bundleRestore A₀.tensorTriv i
            (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))) ∧
        (∀ p, Function.Injective (mfderiv planeModel spaceModel V p)) ∧
        (∀ p, ∃ v w : SmallModes.Base,
          RealModes.realSecondForm (coordinateMap V p) v w (coordinateCenter p) ≠ 0) ∧
        (∀ j x, x ∈ (modeSupport (data.A.chartWeightCompact j) : Set SmallModes.Base) →
          cB < ‖RealModes.realSecondTensor (spaceCoordinates ∘ data.A.vectorPlaneRead j V) x‖) ∧
        (∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
          let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (A₀.vectorChartRead i V ∘ e.symm) p
          NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧
            c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖) ∧
        (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        (∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G) ∧
        ∃ hGs : ContMDiff planeModel spaceModel ∞ G,
        ∃ hGO : MapsTo (lowJet (A₀.jetChartMap i G ∘ e.symm)) S O,
          ∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
            let geom := l.geometry (A₀.jetChartMap i G ∘ e.symm)
              ((A₀.jetChartMap_smooth i hGs).comp hi) hGO
            let t : Period := ((ℓ p/z : ℝ) : Period)
            ‖SurfaceVelocityFamily.Loop.primitiveJetProfile
                (A₀.vectorChartRead i V ∘ e.symm) z p-
              ![geom.longitudinal.val p t,geom.Y p,geom.C p,
                (geom.longitudinal.slow (coordinateVector 1)).val p t,geom.V.angle.val p t]‖ ≤
              Dp*z/(z^b)^lp := by
  obtain ⟨ρ,Q',hρ,hQ',hQ'O,hnear⟩ := A₀.nonlinear_lowJet_neighborhood_of_C2 i hF hi
    S.isOpen hSc hQ O.isOpen hQO hFQ
  obtain ⟨ε,c,hε,hc,hnallOrders⟩ := l.all_orders_primitive_normal_geometry (S := S)
    hQ' hQ'O ℓ hℓx hℓy
  obtain ⟨Dt,hDt,htransport⟩ := A₀.phase_normal_margin i e he hi hcover
  have hcLocal : 0 < c/Dt := div_pos hc hDt
  obtain ⟨ρg,hρg,hgeometry⟩ := data.independent_supported_patch_geometry A₀ houter hF i
  obtain ⟨ρB,cB,hρB,hcB,hmargin⟩ := data.independent_primitive_atlas_normal_margin A₀ houter hF i hcLocal
  obtain ⟨V₀,hV₀,hF₀⟩ := A₀.exists_shifted_bound 2 0 hF
  refine ⟨c,cB,V₀+1,hc,hcB,by positivity,?_⟩
  intro R N
  obtain ⟨Pol,hPol,lm,hconstruct⟩ := A₀.supported_phase_primitive_metric i e he hi hχ hχc hχs
    l ha hamp S hTS hQ' hQ'O (N+(R+2)) ℓ hℓx hℓy
  obtain ⟨ln,hnb⟩ := hnallOrders (N+(R+2))
  obtain ⟨lp,hpb⟩ := l.uniform_primitive_five_profiles (S := S) hQ' hQ'O
    (N+(R+2)) ℓ hℓx hℓy
  let loss := max (max lm ln) lp
  have hcap : 0 < 1/(1+(loss : ℝ)) := by positivity
  have hPol' := cutoffTensorPolynomial_smooth hχ (tensorPolynomialCoordinatePullback_smooth hPol he hi)
  obtain ⟨b,u,η,L,C,P,hb,hb16,hbl,hu,hη,hη1,hL,hC,hP,hmean⟩ :=
    data.polynomial_mean_approximation_in_atlas A₀ (A₀.primitiveAtlasPolynomial i
      (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback Pol e e.symm)))
      (A₀.primitiveAtlasPolynomial_smooth i hPol') hF hmetric (R+2) (N+(R+2))
      (1/(1+(loss : ℝ))) hcap
  have hblm : b < 1/(1+(lm : ℝ)) := hbl.trans_le
    (one_div_le_one_div_of_le (by positivity)
      (by dsimp [loss]; exact_mod_cast Nat.add_le_add_left ((Nat.le_max_left lm ln).trans (Nat.le_max_left _ _)) 1))
  have hbln : b < 1/(1+(ln : ℝ)) := hbl.trans_le
    (one_div_le_one_div_of_le (by positivity)
      (by dsimp [loss]; exact_mod_cast Nat.add_le_add_left ((Nat.le_max_right lm ln).trans (Nat.le_max_left _ _)) 1))
  have hblp : b < 1/(1+(lp : ℝ)) := hbl.trans_le
    (one_div_le_one_div_of_le (by positivity)
      (by dsimp [loss]; exact_mod_cast Nat.add_le_add_left (Nat.le_max_right (max lm ln) lp) 1))
  obtain ⟨η₀,hη₀,_,hsmall⟩ := ExactCorrection.positive_power_threshold L u ρ hu hρ
  obtain ⟨ηg,hηg,_,hgsmall⟩ := ExactCorrection.positive_power_threshold L u ρg hu hρg
  obtain ⟨ηB,hηB,_,hBsmall⟩ := ExactCorrection.positive_power_threshold L u ρB hu hρB
  obtain ⟨_,B,_,hB,hprofiles⟩ := A₀.nonlinear_jet_profiles i hi S.isOpen hSc P hP
  obtain ⟨Dmap,D,hDmap,hD,hprimitive⟩ := hconstruct (R+2) (B ((R+2)+(2*(N+(R+2)+1)+1))) (hB _)
  obtain ⟨Dn,_,hnormal⟩ := hnb (B ((2*(N+(R+2))+2)+2)) (hB _)
  obtain ⟨Dp,hDp,hprofile⟩ := hpb (B ((2*(N+(R+2))+2)+2)) (hB _)
  obtain ⟨ηn,hηn,_,hnsmall⟩ := primitive_normal_threshold hb hbln hε Dn
  obtain ⟨ηs,hηs,_,hslowzero⟩ := ExactCorrection.positive_power_threshold L u (1/2) hu (by norm_num)
  obtain ⟨ηv,hηv,_,hinczero⟩ := primitive_normal_threshold hb hblm (by norm_num : (0:ℝ) < 1/2) Dmap
  let ηold := min η (min η₀ (min ηn (min ηg ηB)))
  have hηold : 0 < ηold := lt_min hη (lt_min hη₀ (lt_min hηn (lt_min hηg hηB)))
  refine ⟨lp,b,u,min ηold (min ηs ηv),L,C+D,P 0+P R+Dmap,Dp,P,hb,hb16,hu,
    lt_min hηold (lt_min hηs hηv),
    (min_le_left _ _).trans ((min_le_left _ _).trans hη1),hL,add_nonneg hC hD,
    add_nonneg (add_nonneg (hP 0) (hP R)) hDmap,hDp,hblp,hP,?_⟩
  intro z hz hznew
  have hzη : z < ηold := hznew.trans_le (min_le_left _ _)
  have hzs0 : z < ηs := hznew.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hzv0 : z < ηv := hznew.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hzη' : z < η := hzη.trans_le (min_le_left _ _)
  have hz1 : z ≤ 1 := hzη'.le.trans hη1
  have hs : 0 < z^b := Real.rpow_pos_of_pos hz _
  have hs1 : z^b ≤ 1 := Real.rpow_le_one hz.le hz1 hb
  have hzs : z ≤ z^b := by
    have hb1 : b ≤ 1 := by linarith
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hz hz1 hb1
  obtain ⟨G,hG,hclose,hmap,hmean⟩ := hmean z hz hzη'
  have hGQ : MapsTo (lowJet (A₀.jetChartMap i G ∘ e.symm)) S Q' :=
    hnear G hG (fun j => ((hclose j).mono_order (by omega)).mono_const
      (hsmall z hz (hzη.trans_le ((min_le_right _ _).trans (min_le_left _ _)))).le)
  have hGv : ∀ p ∈ S, p ∉ K → ∀ t,
      l.velocity (lowJet (A₀.jetChartMap i G ∘ e.symm) p,t) =
        SurfaceVelocityFamily.normal (lowJet (A₀.jetChartMap i G ∘ e.symm) p) := by
    intro p hp hpK t
    exact hv _ (hQ'O (hGQ hp)) (by simpa only [lowJetPosition_lowJet] using hpK) t
  obtain ⟨U,hzero,hUs,hrep,hinit,hVs,herror⟩ := hprimitive G hG hGQ K hK hKS hKA hone hGv
  let V := A₀.phaseAtlasAnsatz i G e χ U ℓ (N+(R+2)+1) z
  have hjet := (hprofiles G hG ⟨z^b,hs.le⟩ hs hs1 hmap).2 ((R+2)+(2*(N+(R+2)+1)+1))
  have hsolved : A₀.TensorWeightedBound z (R+2) (C*z^(N+(R+2)))
      (A₀.atlasPolynomialMetric (A₀.primitiveAtlasPolynomial i
        (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback Pol e e.symm))) z G-g.inner) :=
    fun j => (hmean j).shrink_scale hz.le hz1
  have herr := (herror (z^b) z hz hzs hs1 hjet).2 g.inner g.contMDiff (C*z^(N+(R+2))) hsolved
  have htot : 0 ≤ C*z^(N+(R+2))+D*z^(N+(R+2)+1)/(z^b)^lm := by positivity
  have hfinal := A₀.tensorWeightedBound_unscaled hz hz1 htot herr
  have hincrement := (herror (z^b) z hz hzs hs1 hjet).1
  have hsmallinc : Dmap*z/(z^b)^lm ≤ Dmap := by
    apply (div_le_iff₀ (pow_pos hs _)).mpr
    exact mul_le_mul_of_nonneg_left (slow_power_dominates_fast hz hz1 hb hblm) hDmap
  have hGweighted := A₀.weighted_of_shifted_two hz.le hzs hs1 (hmap R)
  have hincweighted : A₀.WeightedBound z R Dmap (V-G) :=
    fun j => ((hincrement j).mono_order (by omega)).mono_const hsmallinc
  have hVweighted := A₀.weightedBound_add hG ((hVs z).sub hG) hz.le hGweighted hincweighted
  have hvadd : G+(V-G) = V := by abel
  change A₀.WeightedBound z R (P R+Dmap) (G+(V-G)) at hVweighted
  rw [hvadd] at hVweighted
  have hVweighted' : A₀.WeightedBound z R (P 0+P R+Dmap) V :=
    fun j => (hVweighted j).mono_const (by linarith [hP 0])
  have hshift := A₀.weighted_to_shifted (q := 2) (m := R) hz hz1
    (show 0 ≤ Dmap*z/(z^b)^lm by positivity)
    (show A₀.WeightedBound z (2+R) (Dmap*z/(z^b)^lm) (V-G) from by
      simpa only [V,Nat.add_comm R 2] using hincrement)
  have hshift' : A₀.ShiftedBound 2 R z (Dmap/z^2) (V-G) := by
    intro j k hk x
    exact (hshift j k hk x).trans (div_le_div_of_nonneg_right hsmallinc (sq_nonneg z))
  have hvmap := A₀.shifted_map_recurrence hG ((hVs z).sub hG)
    (hmap 0) (hmap R) hshift' hs hz.le hzs (hP 0) (hP R)
  change A₀.ShiftedBound 2 R z (P 0+(z/(z^b))*P R+Dmap/z^2) (G+(V-G)) at hvmap
  rw [hvadd] at hvmap
  have hvmap' : A₀.ShiftedBound 2 R z ((P 0+P R+Dmap)/z^2) V := by
    intro j k hk x
    exact (hvmap j k hk x).trans (primitive_shifted_budget hz hz1 hzs (hP 0) (hP R) hDmap)
  have hnall : ∀ p ∈ (S : Set JetPolynomial.Base) ∩ e.target,
      let H := SurfaceVelocityFamily.Loop.primitiveNormalTriple (A₀.vectorChartRead i V ∘ e.symm) p
      NormalFrame.gramDet (H 0) (H 1) ≠ 0 ∧ c < ‖RealModes.realNormalPart (H 0) (H 1) (H 2)‖ := by
    intro p hp
    have heq := A₀.phaseAtlasAnsatz_normalTriple i G e hi hχs U hK hKA hzero hone ℓ
      (N+(R+2)+1) z hp.2
    change NormalFrame.gramDet _ _ ≠ 0 ∧ c < ‖_‖
    rw [show SurfaceVelocityFamily.Loop.primitiveNormalTriple (A₀.vectorChartRead i V ∘ e.symm) p =
      SurfaceVelocityFamily.Loop.primitiveNormalTriple
        (finiteAnsatz (A₀.vectorChartRead i G ∘ e.symm) U ℓ (N+(R+2)+1) z) p from heq]
    have hh := hnormal (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi)
      hGQ (z^b) z hz hzs hs1
      ((hprofiles G hG ⟨z^b,hs.le⟩ hs hs1 hmap).2 ((2*(N+(R+2))+2)+2))
      (hnsmall z hz (hzη.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
      U hUs hrep hinit p hp.1
    have heuc : (fun q => JetVelocityCoordinates.toEuclidean ((A₀.jetChartMap i G ∘ e.symm) q)) =
      A₀.vectorChartRead i G ∘ e.symm := by
      funext q
      exact spaceCoordinates.symm_apply_apply _
    rw [heuc] at hh
    exact hh
  have hext : ∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G := by
    intro p hp
    exact A₀.phaseAtlasAnsatz_eventuallyEq i G e hi hχs U hK hKA hzero ℓ (N+(R+2)+1) z hp
  have hextK : ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
    intro p hp
    exact A₀.phaseAtlasAnsatz_eventuallyEq_precise i G e hi hχs U hK hzero ℓ
      (N+(R+2)+1) z hp
  have hlocal : ∀ p ∈ tsupport (A₀.weight i),
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A₀.vectorPlaneRead i V)
        (planeCoordinateIsometry (chart (i : M) p))) ∧
      c/Dt < ‖RealModes.realSecondTensor (spaceCoordinates ∘ A₀.vectorPlaneRead i V)
        (planeCoordinateIsometry (chart (i : M) p))‖ := by
    intro p hp
    have hx : chart (i : M) p ∈ (A₀.chartWeightCompact i : Set JetPolynomial.Base) := ⟨p,hp,rfl⟩
    exact htransport V (hVs z) _ hx c hc
      (hnall _ ⟨hTS (hcover hx),e.map_source (hcover hx)⟩)
  have hglobal := hgeometry G V hG (hVs z) (L*z^u) (by positivity)
    (hgsmall z hz (hzη.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))))
    (fun j => (hclose j).mono_order (by omega))
    (fun p hp => ⟨(hlocal p hp).1,norm_pos_iff.mp (hcLocal.trans (hlocal p hp).2)⟩) hext
  have hBglobal := hmargin G V hG (hVs z) hglobal.1 (L*z^u) (by positivity)
    (hBsmall z hz (hzη.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))))
    (fun j => (hclose j).mono_order (by omega)) (fun p hp => (hlocal p hp).2) hext
  have hFzero : A₀.WeightedBound 1 0 V₀ F := by
    intro j k hk x hx
    have hk0 : k = 0 := by omega
    subst k
    simpa only [one_pow,one_mul,iteratedFDerivWithin_univ] using hF₀ j 0 (by omega) x
  have hslow0 : A₀.WeightedBound 1 0 (1/2) (G-F) := fun j =>
    ((hclose j).mono_order (Nat.zero_le _)).mono_const (hslowzero z hz hzs0).le
  have hinc0 : A₀.WeightedBound 1 0 (1/2) (V-G) := by
    intro j k hk x hx
    have hk0 : k = 0 := by omega
    subst k
    have hh := hincrement j 0 (by omega) x hx
    simp only [pow_zero,one_mul] at hh ⊢
    exact hh.trans (hinczero z hz hzv0).le
  have hsum0 := A₀.weightedBound_add hF (hG.sub hF) zero_le_one hFzero hslow0
  have hsum1 := A₀.weightedBound_add (hF.add (hG.sub hF)) ((hVs z).sub hG)
    zero_le_one hsum0 hinc0
  have hVzero : A₀.WeightedBound 1 0 (V₀+1) V := by
    change A₀.WeightedBound 1 0 (V₀+1/2+1/2) (F+(G-F)+(V-G)) at hsum1
    have hsumid : F+(G-F)+(V-G) = V := by abel
    rw [hsumid] at hsum1
    convert hsum1 using 1 <;> first | rfl | ring
  refine ⟨G,V,hG,hVs z,hclose,hmap,hVweighted',hVzero,hvmap',?_,hglobal.1,hglobal.2,hBglobal,hnall,hext,hextK,?_⟩
  · intro j
    apply ((hfinal j).mono_order (by omega)).mono_const
    have hlead : C*z^(N+(R+2))/z^(R+2) = C*z^N := by
      rw [pow_add,← mul_assoc,mul_div_cancel_right₀ _ (pow_ne_zero _ hz.ne')]
    rw [add_div,hlead]
    have htail := mul_le_mul_of_nonneg_left
      (primitive_tail_power_bound (N := N) (R := R+2) hz hz1 hb hblm) hD
    have heq : D*z^(N+(R+2)+1)/(z^b)^lm/z^(R+2) = D*(z^(N+(R+2)+1)/(z^b)^lm/z^(R+2)) := by ring
    rw [heq]
    calc
      C*z^N+D*(z^(N+(R+2)+1)/(z^b)^lm/z^(R+2)) ≤ C*z^N+D*z^N := add_le_add le_rfl htail
      _ = (C+D)*z^N := by ring

  · refine ⟨hG,fun p hp => hQ'O (hGQ hp),?_⟩
    intro p hp
    change ‖SurfaceVelocityFamily.Loop.primitiveJetProfile
      (A₀.vectorChartRead i V ∘ e.symm) z p - _‖ ≤ _
    rw [show SurfaceVelocityFamily.Loop.primitiveJetProfile
        (A₀.vectorChartRead i V ∘ e.symm) z p =
        SurfaceVelocityFamily.Loop.primitiveJetProfile
          (finiteAnsatz (A₀.vectorChartRead i G ∘ e.symm) U ℓ (N+(R+2)+1) z) z p from
      A₀.phaseAtlasAnsatz_jetProfile i G e hi hχs U hK hKA hzero hone ℓ
        (N+(R+2)+1) z hp.2]
    have hh := hprofile (A₀.jetChartMap i G ∘ e.symm)
      ((A₀.jetChartMap_smooth i hG).comp hi) hGQ (z^b) z hz hzs hs1
      ((hprofiles G hG ⟨z^b,hs.le⟩ hs hs1 hmap).2 ((2*(N+(R+2))+2)+2))
      U hUs hrep hinit p hp.1
    have heuc : (fun q => JetVelocityCoordinates.toEuclidean ((A₀.jetChartMap i G ∘ e.symm) q)) =
        A₀.vectorChartRead i G ∘ e.symm := by
      funext q
      exact spaceCoordinates.symm_apply_apply _
    rw [heuc] at hh
    exact hh

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_profiled_phase_primitive_realization_oai.{u_1}
