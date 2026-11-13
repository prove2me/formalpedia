-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:38:36.080505+00:00
-- url     : https://prove2.me/submissions/8db2757f-54e5-4a5e-a920-fa9d0a05f4b5

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_independent_exact_phase_primitive_five_profiles

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
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_NormalJets
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
open ClosedSurfaceR4.SmallModes
open ClosedSurfaceR4.WeightedEstimates

lemma contDiff_realTwoJet {F : RField 4} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (realTwoJet F) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i
  · exact contDiff_real_coordDeriv hF dx
  · exact contDiff_real_coordDeriv hF dy
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dx) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dx
  · exact contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy




end ClosedSurfaceR4.RealModes

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_SecondForms
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Complex Bundle Manifold
open scoped ContDiff Matrix Topology Manifold BigOperators

namespace ClosedSurfaceR4.RealModes
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.PhaseGeometry Set

lemma real_second_coordDeriv {n : ℕ} {F : RField n} {p : Base}
    (hF : DifferentiableAt ℝ (fderiv ℝ F) p) (v w : Base) :
    coordDeriv v (coordDeriv w F) p = fderiv ℝ (fderiv ℝ F) p v w := by
  have h := (hF.hasFDerivAt.clm_apply (hasFDerivAt_const w p)).fderiv
  change (fderiv ℝ (fun q => (fderiv ℝ F q) w) p) v = _
  rw [h]
  simp

lemma real_second_coordDeriv_comm {n : ℕ} {F : RField n} (hF : ContDiff ℝ ∞ F)
    (p v w : Base) : coordDeriv v (coordDeriv w F) p = coordDeriv w (coordDeriv v F) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) p :=
    ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt
  rw [real_second_coordDeriv hd, real_second_coordDeriv hd]
  exact second_derivative_symmetric
    (fun q => (hF.differentiable (by simp) q).hasFDerivAt) hd.hasFDerivAt v w

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LowJetChainRule
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mapCoeff _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The chain rule for coefficients depending on position and the actual
second jet of a map from a surface chart into four-space. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates

lemma lowJet_derivative {G : Base → Space} (hG : ContDiff ℝ ∞ G) (v : Fin 2) (p : Base) :
    fderiv ℝ (lowJet G) p (coordinateVector v) = lowDerivative G v p := by
  ext i
  have h := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
    (fderiv_apply ((lowJet_smooth hG).differentiable (by simp) p) i)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    lowJet_coordinate_derivative] using h.symm

end ClosedSurfaceR4.JetPolynomial

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

lemma slowOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) (t : ℝ) :
    slowOn F S hS hF v p (t : Period) =
      slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t) :=
  bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicCalculus

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFamilies
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth periodic coefficient families on the actual open geometric domain.
Values outside that domain are fixed at zero, so equality only needs checking inside. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
variable (O : TopologicalSpace.Opens A) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {O E}
namespace Family

@[simp] lemma slow_apply (F : Family O E) (v : A) {p : A} (hp : p ∈ O) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      SmoothPeriodicCalculus.slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := by
  rw [slow, ofLocal_apply _ _ hp, slowOn_apply _ _ _ _ _ hp]

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicFastEvaluation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual fast-phase differentiation on an admissible chart domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector SmoothPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {O : TopologicalSpace.Opens A}

lemma angle_apply (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    F.angle.val p (t : Period) =
      angleDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) (p, t) := by
  rw [angle, ofLocal_apply _ _ hp]
  exact LocalPeriodicCalculus.bundleOn_apply _ _ _ _ _ hp t

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_JetVelocityLoop
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A controlled loop on a neighborhood of the actual second-jet section.
Its translation depends on position alone, so the prescribed turn derivatives
along the original section persist under the joint density construction. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.CollarVelocity
open RealModes TransverseSmallFunction

lemma jetSection_smooth {F : RField 4} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (jetSection F) := contDiff_id.prodMk (contDiff_realTwoJet hF)

end ClosedSurfaceR4.CollarVelocity

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SurfaceJetCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translate the geometric surface jets to the coordinates used by the
quantitative finite-polynomial construction. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.SurfaceJetCoordinates
open RealModes SmallModes WeightedEstimates

lemma directional_chart (f : Base → ℝ) (hf : ContDiff ℝ ∞ f) (w : List (Fin 2)) :
    iteratedDirectional (w.map JetPolynomial.coordinateVector) (f ∘ baseEquiv) =
      (iteratedDirectional (w.map (fun i => baseEquiv (JetPolynomial.coordinateVector i))) f) ∘ baseEquiv := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [List.map_cons, iteratedDirectional]
    rw [ih]
    funext p
    have hs : ContDiff ℝ ∞
        (iteratedDirectional (w.map (fun i => baseEquiv (JetPolynomial.coordinateVector i))) f) :=
      contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hf.contDiffOn _)
    rw [fderiv_comp p (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) baseEquiv.differentiableAt,
      baseEquiv.fderiv, ContinuousLinearMap.comp_apply]
    rfl

lemma directional_component {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (w : List Base) (a : Fin 4) :
    iteratedDirectional w (fun p => F p a) = fun p => iteratedDirectional w F p a := by
  induction w with
  | nil => rfl
  | cons v w ih =>
    simp only [iteratedDirectional]
    rw [ih]
    funext p
    have hs : ContDiff ℝ ∞ (iteratedDirectional w F) :=
      contDiffOn_univ.mp (contDiffOn_iteratedDirectional isOpen_univ hF.contDiffOn w)
    rw [fderiv_apply (hs.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) a]
    rfl

theorem decode_lowJet {F : RField 4} (hF : ContDiff ℝ ∞ F) (p : JetPolynomial.Base) :
    decode (JetPolynomial.lowJet (F ∘ baseEquiv) p) = CollarVelocity.jetSection F (baseEquiv p) := by
  apply Prod.ext
  · rfl
  · funext i a
    change JetPolynomial.jet (F ∘ baseEquiv) (JetPolynomial.lowWord (![1, 2, 3, 4, 6] i)) a p =
      realTwoJet F (baseEquiv p) i a
    have he (w : List (Fin 2)) : JetPolynomial.jet (F ∘ baseEquiv) w a p =
        iteratedDirectional (w.map (fun j => baseEquiv (JetPolynomial.coordinateVector j))) F (baseEquiv p) a := by
      change iteratedDirectional (w.map JetPolynomial.coordinateVector)
        ((fun q => F q a) ∘ baseEquiv) p = _
      rw [directional_chart _ (contDiff_pi.mp hF a) w, Function.comp_apply, directional_component hF]
    rw [he]
    fin_cases i <;> simp [JetPolynomial.lowWord, realTwoJet, iteratedDirectional, coordDeriv,
      JetPolynomial.coordinateVector, dx, dy] <;> rfl

end ClosedSurfaceR4.SurfaceJetCoordinates

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CompactCompositionBound
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

theorem compact_composition_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    {S : Set Base} (hS : IsOpen S) (hSc : IsCompact (closure S)) (m : ℕ) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ (f : Base → E) (C : ℝ),
      0 ≤ C → ContDiff ℝ ∞ f → WeightedBound univ 1 m C f →
      WeightedBound S 1 m (D*C) (f ∘ T) := by
  obtain ⟨B,hB,hTb⟩ := compact_local_weighted_bound hS isOpen_univ hSc
    subset_closure (subset_univ _) hT.contDiffOn m
  let D : ℝ := (m.factorial : ℝ)*B^m
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le
    (by exact_mod_cast Nat.factorial_pos m) (one_le_pow₀ hB)
  refine ⟨D,hD,?_⟩
  intro f C hC hf hb
  have hcoord : ∀ k, 1 ≤ k → k ≤ m → ∀ x ∈ S,
      ‖iteratedFDerivWithin ℝ k T S x‖ ≤ B := by
    intro k _ hk x hx
    simpa only [one_pow,one_mul] using hTb 1 zero_le_one le_rfl k hk x hx
  have hh := hb.comp_coordinates hS.uniqueDiffOn uniqueDiffOn_univ zero_lt_one le_rfl
    hB hC hT.contDiffOn hf.contDiffOn (fun _ _ => mem_univ _) hcoord
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  dsimp only [D]
  ring

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_VelocityCoordinateData
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smooth velocity coordinates and their calibrated collar values. -/
noncomputable section
open Set
open scoped ContDiff Matrix

namespace ClosedSurfaceR4.VelocityFrame
open NormalFrame

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma velocityRadius_smoothOn {v : E → Vec} {a : E → ℝ} {U : Set E}
    (hv : ContDiffOn ℝ ∞ v U) (ha : ContDiffOn ℝ ∞ a U)
    (hn : ∀ x ∈ U, v x ≠ 0 ∨ a x ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => velocityRadius (v x) (a x)) U := by
  apply ((dot_smoothOn hv hv).add (ha.pow 2)).sqrt
  intro x hx
  have hp := velocityRadius_pos (hn x hx)
  exact (Real.sqrt_pos.mp hp).ne'

end ClosedSurfaceR4.VelocityFrame

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

end Loop
end ClosedSurfaceR4.SurfaceVelocityFamily

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_BoundaryProfileCoordinates
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five Euclidean profiles used by the exact primitive determine the
canonical normal frame in the real surface coordinates. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open RealModes NormalFrame SurfaceJetCoordinates JetVelocityCoordinates
open SurfaceVelocityFamily.Loop

private lemma directional_euclidean_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (v : JetPolynomial.Base) :
    PeriodicExpansion.directionalMap (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) v =
      fun q => JetVelocityCoordinates.toEuclidean (SmallModes.coordDeriv (baseEquiv v) F (baseEquiv q)) := by
  funext q
  change fderiv ℝ ((JetVelocityCoordinates.toEuclidean ∘ F) ∘ baseEquiv) q v = _
  rw [fderiv_comp q ((JetVelocityCoordinates.toEuclidean.contDiff.comp hF).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)
    baseEquiv.differentiableAt,ContinuousLinearMap.comp_apply,baseEquiv.fderiv]
  rw [fderiv_comp (baseEquiv q) JetVelocityCoordinates.toEuclidean.differentiableAt
    (hF.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),ContinuousLinearMap.comp_apply,JetVelocityCoordinates.toEuclidean.fderiv]
  rfl

lemma boundaryProfileMap_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (z : ℝ) (p : JetPolynomial.Base) :
    boundaryProfileMap (primitiveJetProfile (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) z p) =
      realBoundaryProfile F z (baseEquiv p) := by
  have hfirst (v : JetPolynomial.Base) := directional_euclidean_chart hF v
  have hsecond (v w : JetPolynomial.Base) :
      PeriodicExpansion.directionalMap
        (PeriodicExpansion.directionalMap (fun q => JetVelocityCoordinates.toEuclidean (F (baseEquiv q))) v) w =
      fun q => JetVelocityCoordinates.toEuclidean (SmallModes.coordDeriv (baseEquiv w)
        (SmallModes.coordDeriv (baseEquiv v) F) (baseEquiv q)) := by
    rw [hfirst]
    exact directional_euclidean_chart (contDiff_real_coordDeriv hF _) w
  funext j
  fin_cases j
  · change spaceCoordinates (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0) p) = _
    rw [hfirst]
    simp only [baseEquiv_zero,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 1) p) = _
    rw [hfirst]
    simp only [baseEquiv_one,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 1))
      (JetPolynomial.coordinateVector 1) p) = _
    rw [hsecond]
    simp only [baseEquiv_one,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl
  · change spaceCoordinates (PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0))
      (JetPolynomial.coordinateVector 1) p) = _
    rw [hsecond]
    simp only [baseEquiv_zero,baseEquiv_one,JetVelocityCoordinates.toEuclidean,
      ContinuousLinearEquiv.apply_symm_apply]
    exact real_second_coordDeriv_comm hF (baseEquiv p) SmallModes.dy SmallModes.dx
  · change spaceCoordinates (z • PeriodicExpansion.directionalMap
      (PeriodicExpansion.directionalMap _ (JetPolynomial.coordinateVector 0))
      (JetPolynomial.coordinateVector 0) p) = _
    rw [hsecond,map_smul]
    simp only [baseEquiv_zero,JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    rfl

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LeadingProfileMap
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five leading profiles depend smoothly on the second jet, its first
transverse derivative, and the periodic parameter. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma leadingVelocity_smooth : ContDiffOn ℝ ∞ l.leadingVelocity (O ×ˢ univ) :=
  (l.smoothTangent.comp contDiffOn_fst (fun _ hz => hz.1)).add l.smoothVelocity

lemma leadingProfileMap_smooth :
    ContDiffOn ℝ ∞ l.leadingProfileMap ((O ×ˢ univ) ×ˢ univ) := by
  have hJ : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => z.1.1) ((O ×ˢ univ) ×ˢ univ) :=
    contDiffOn_fst.fst
  have hV : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => l.leadingVelocity z.1)
      ((O ×ˢ univ) ×ˢ univ) :=
    l.leadingVelocity_smooth.comp contDiffOn_fst (fun _ hz => hz.1)
  have hdV : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => fderiv ℝ l.leadingVelocity z.1)
      ((O ×ˢ univ) ×ˢ univ) := (l.leadingVelocity_smooth.fderiv_of_isOpen
    (O.isOpen.prod isOpen_univ) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp contDiffOn_fst (fun _ hz => hz.1)
  have hdW : ContDiffOn ℝ ∞ (fun z : LeadingProfileInput => fderiv ℝ l.velocity z.1)
      ((O ×ˢ univ) ×ˢ univ) := (l.smoothVelocity.fderiv_of_isOpen
    (O.isOpen.prod isOpen_univ) (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).comp contDiffOn_fst (fun _ hz => hz.1)
  apply contDiffOn_pi.mpr
  intro i
  fin_cases i
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn hV
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn ((slot_smooth 2).contDiffOn.comp hJ (fun _ _ => mem_univ _))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn ((slot_smooth 6).contDiffOn.comp hJ (fun _ _ => mem_univ _))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn
      (hdV.clm_apply (contDiffOn_snd.prodMk contDiffOn_const))
  · exact JetVelocityCoordinates.toEuclidean.contDiff.comp_contDiffOn
      (hdW.clm_apply contDiffOn_const)

lemma leadingProfileMap_continuousAt {z : LeadingProfileInput} (hz : z.1.1 ∈ O) :
    ContinuousAt l.leadingProfileMap z :=
  (l.leadingProfileMap_smooth.contDiffAt
    (((O.isOpen.prod isOpen_univ).prod isOpen_univ).mem_nhds
      ⟨⟨hz,mem_univ _⟩,mem_univ _⟩)).continuousAt

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LeadingProfileIdentification
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite-dimensional leading-profile map evaluates to the exact
geometric velocity and its derivatives in the primitive construction. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation CovarianceCorrector
open LocalPeriodicExpansion
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

private lemma jet_parameter_pullback_derivative {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (c : LowJet × ℝ → RealModes.RVec 4)
    (p : JetPolynomial.Base) (t : ℝ) (hc : DifferentiableAt ℝ c (lowJet G p,t))
    (v : JetPolynomial.Base) (a : ℝ) :
    fderiv ℝ (fun q : JetPolynomial.Base × ℝ =>
      JetVelocityCoordinates.toEuclidean (c (lowJet G q.1,q.2))) (p,t) (v,a) =
      JetVelocityCoordinates.toEuclidean (fderiv ℝ c (lowJet G p,t)
        (fderiv ℝ (lowJet G) p v,a)) := by
  have hlow : HasFDerivAt (lowJet G) (fderiv ℝ (lowJet G) p) p :=
    ((lowJet_smooth hG).differentiable (by simp) p).hasFDerivAt
  have hfirst : HasFDerivAt (fun q : JetPolynomial.Base × ℝ => lowJet G q.1)
      ((fderiv ℝ (lowJet G) p).comp (ContinuousLinearMap.fst ℝ JetPolynomial.Base ℝ)) (p,t) :=
    by
      simpa only [Function.comp_def] using
        (hlow.comp (p,t) (hasFDerivAt_fst (𝕜 := ℝ) (p := (p,t))))
  have hP : HasFDerivAt (fun q : JetPolynomial.Base × ℝ => (lowJet G q.1,q.2))
      (((fderiv ℝ (lowJet G) p).comp (ContinuousLinearMap.fst ℝ JetPolynomial.Base ℝ)).prod
        (ContinuousLinearMap.snd ℝ JetPolynomial.Base ℝ)) (p,t) :=
    hfirst.prodMk (ContinuousLinearMap.snd ℝ JetPolynomial.Base ℝ).hasFDerivAt
  have hd := ((JetVelocityCoordinates.toEuclidean.hasFDerivAt.comp (lowJet G p,t)
    hc.hasFDerivAt).comp (p,t) hP).fderiv
  change (fderiv ℝ ((JetVelocityCoordinates.toEuclidean ∘ c) ∘
    (fun q : JetPolynomial.Base × ℝ => (lowJet G q.1,q.2))) (p,t)) (v,a) = _
  rw [hd]
  rfl

lemma geometry_longitudinal_value {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    (l.geometry G hG hGO).longitudinal.val p (t : Period) =
      JetVelocityCoordinates.toEuclidean (l.leadingVelocity (lowJet G p,t)) := by
  rw [Geometry.longitudinal,Family.add_apply,Family.constant_apply _ _ hp,
    l.geometry_velocity hG hGO hp,l.euclideanVelocity_apply (hGO hp)]
  exact (map_add JetVelocityCoordinates.toEuclidean _ _).symm

/-- All five entries depend on the third jet only through the single
transverse derivative of the second jet. -/
theorem leadingProfileMap_geometry {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    l.leadingProfileMap ((lowJet G p,t),lowDerivative G 1 p) =
      ![(l.geometry G hG hGO).longitudinal.val p (t : Period),
        (l.geometry G hG hGO).Y p,(l.geometry G hG hGO).C p,
        ((l.geometry G hG hGO).longitudinal.slow (coordinateVector 1)).val p (t : Period),
        (l.geometry G hG hGO).V.angle.val p (t : Period)] := by
  have hlong : (fun q : JetPolynomial.Base × ℝ =>
      (l.geometry G hG hGO).longitudinal.val q.1 (q.2 : Period)) =ᶠ[𝓝 (p,t)]
      (fun q => JetVelocityCoordinates.toEuclidean (l.leadingVelocity (lowJet G q.1,q.2))) := by
    filter_upwards [(S.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ t⟩] with q hq
    exact l.geometry_longitudinal_value hG hGO hq.1 q.2
  have hvel : (fun q : JetPolynomial.Base × ℝ =>
      (l.geometry G hG hGO).V.val q.1 (q.2 : Period)) =ᶠ[𝓝 (p,t)]
      (fun q => JetVelocityCoordinates.toEuclidean (l.velocity (lowJet G q.1,q.2))) := by
    filter_upwards [(S.isOpen.prod isOpen_univ).mem_nhds ⟨hp,mem_univ t⟩] with q hq
    rw [l.geometry_velocity hG hGO hq.1,l.euclideanVelocity_apply (hGO hq.1)]
  have hmem : (lowJet G p,t) ∈ (O : Set LowJet) ×ˢ univ := ⟨hGO hp,mem_univ t⟩
  have hW := (l.leadingVelocity_smooth.contDiffAt
    ((O.isOpen.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hV := (l.smoothVelocity.contDiffAt
    ((O.isOpen.prod isOpen_univ).mem_nhds hmem)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  funext i
  fin_cases i
  · exact (l.geometry_longitudinal_value hG hGO hp t).symm
  · rfl
  · rfl
  · change JetVelocityCoordinates.toEuclidean
        (fderiv ℝ l.leadingVelocity (lowJet G p,t) (lowDerivative G 1 p,0)) =
      ((l.geometry G hG hGO).longitudinal.slow (coordinateVector 1)).val p (t : Period)
    rw [Family.slow_apply _ _ hp]
    change _ = fderiv ℝ _ (p,t) (coordinateVector 1,0)
    rw [hlong.fderiv_eq,jet_parameter_pullback_derivative hG _ p t hW,
      lowJet_derivative hG]
  · change JetVelocityCoordinates.toEuclidean (fderiv ℝ l.velocity (lowJet G p,t) (0,1)) =
      (l.geometry G hG hGO).V.angle.val p (t : Period)
    rw [Family.angle_apply _ hp]
    change _ = fderiv ℝ _ (p,t) (0,1)
    rw [hvel.fderiv_eq,jet_parameter_pullback_derivative hG _ p t hV,map_zero]

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LeadingInputStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! C3 closeness controls the finite data used by the leading-profile map,
with no loss in the fast phase parameter. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.JetPolynomial
open WeightedEstimates SurfaceVelocityFamily.Loop

lemma lowJet_sub_variation {F G : Base → Space}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    (fun p => lowJet G p-lowJet F p) = variationLowJet (fun x => G x-F x) := by
  funext p
  have he := lowJet_affine hF (hG.sub hF) 1 p
  have hf : (fun q => F q+(1 : ℝ) • (G q-F q)) = G := by
    funext q
    simp only [one_smul]
    abel
  rw [hf,one_smul] at he
  rw [he]
  abel

lemma lowDerivative_sub_variation {F G : Base → Space}
    (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) (i : Fin 2) (p : Base) :
    lowDerivative G i p-lowDerivative F i p =
      fderiv ℝ (variationLowJet (fun x => G x-F x)) p (coordinateVector i) := by
  rw [← lowJet_derivative hG,← lowJet_derivative hF]
  have he := congrArg (fun L : Base →L[ℝ] LowJet => L (coordinateVector i))
    (fderiv_fun_sub ((lowJet_smooth hG).differentiable (by simp) p)
      ((lowJet_smooth hF).differentiable (by simp) p))
  have hh : (fderiv ℝ (fun q => lowJet G q-lowJet F q) p) (coordinateVector i) =
      (fderiv ℝ (lowJet G) p) (coordinateVector i)-
        (fderiv ℝ (lowJet F) p) (coordinateVector i) := he
  rw [lowJet_sub_variation hF hG] at hh
  exact hh.symm

lemma leadingInput_sub_bound {F G : Base → Space} {U : Set Base}
    (hU : IsOpen U) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G)
    {C : ℝ} (hC : 0 ≤ C) (hb : WeightedBound U 1 3 C (fun x => G x-F x))
    {p : Base} (hp : p ∈ U) (t : ℝ) :
    ‖(((lowJet G p,t),lowDerivative G 1 p) : LeadingProfileInput)-
      ((lowJet F p,t),lowDerivative F 1 p)‖ ≤ C := by
  have hv : WeightedBound U 1 1 C (variationLowJet (fun x => G x-F x)) := by
    simpa using weighted_variationLowJet hU (hG.sub hF) zero_lt_one le_rfl hC 1 hb
  have hlow : ‖lowJet G p-lowJet F p‖ ≤ C := by
    rw [show lowJet G p-lowJet F p = variationLowJet (fun x => G x-F x) p from
      congrFun (lowJet_sub_variation hF hG) p]
    exact hv.norm_le hp
  have hd := hv.directional hU zero_lt_one (variationLowJet_smooth (hG.sub hF)).contDiffOn
    (coordinateVector 1)
  have hder : ‖lowDerivative G 1 p-lowDerivative F 1 p‖ ≤ C := by
    rw [lowDerivative_sub_variation hF hG]
    apply (hd.norm_le hp).trans
    simpa only [div_one] using mul_le_of_le_one_left hC (norm_coordinateVector_le 1)
  simpa only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero] using
    (max_le (max_le hlow hC) hder)

end ClosedSurfaceR4.JetPolynomial

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularJetProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identify the canonical boundary profiles with the actual circular loop
in the analytic second-jet coordinates. -/
noncomputable section
open Set Filter
open scoped ContDiff Matrix Topology
namespace ClosedSurfaceR4
namespace GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma circular_angular_derivative {R : E → ℝ} {e₁ e₂ : E → Vec}
    {α : E × ℝ → ℝ} {x : E} {t : ℝ}
    (hR : DifferentiableAt ℝ R x) (h₁ : DifferentiableAt ℝ e₁ x)
    (h₂ : DifferentiableAt ℝ e₂ x) (hα : DifferentiableAt ℝ α (x,t)) :
    fderiv ℝ (fun z : E × ℝ => R z.1 • direction (e₁ z.1) (e₂ z.1) (α z))
      (x,t) (0,1) = (R x*fderiv ℝ α (x,t) (0,1)) •
        angularDirection (e₁ x) (e₂ x) (α (x,t)) := by
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (x,t))
  have hd := (hR.hasFDerivAt.comp (x,t) hf).smul
    ((hα.hasFDerivAt.cos.smul (h₁.hasFDerivAt.comp (x,t) hf)).add
      (hα.hasFDerivAt.sin.smul (h₂.hasFDerivAt.comp (x,t) hf)))
  change HasFDerivAt (fun z : E × ℝ =>
    R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) _ (x,t) at hd
  rw [hd.fderiv]
  ext i
  simp [angularDirection,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
    Function.comp_def]
  ring

end GeometryPreservation

namespace SurfaceVelocityFamily.Loop
open NormalFrame VelocityFrame RealModes JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem circular_leadingProfileMap {R : LowJet → ℝ} {e₁ e₂ : LowJet → Vec}
    {α : LowJet × ℝ → ℝ} (hR : ContDiffOn ℝ ∞ R O)
    (h₁ : ContDiffOn ℝ ∞ e₁ O) (h₂ : ContDiffOn ℝ ∞ e₂ O)
    (hα : ContDiffOn ℝ ∞ α (O ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      R J • direction (e₁ J) (e₂ J) (α (J,t)))
    {J : LowJet} (hJ : J ∈ O) (t : ℝ) (D : LowJet) :
    boundaryProfileMap (l.leadingProfileMap ((J,t),D)) =
      circularFamilyProfile tangent (slot 1) (slot 2) (slot 6) R e₁ e₂ α D (J,t) := by
  have hnb : (O : Set LowJet) ×ˢ (univ : Set ℝ) ∈ 𝓝 (J,t) :=
    (O.isOpen.prod isOpen_univ).mem_nhds ⟨hJ,mem_univ t⟩
  have hvgerm : l.velocity =ᶠ[𝓝 (J,t)]
      (fun z : LowJet × ℝ => R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) := by
    filter_upwards [hnb] with z hz
    exact hvel z.1 hz.1 z.2
  have hlgerm : l.leadingVelocity =ᶠ[𝓝 (J,t)]
      (fun z : LowJet × ℝ => tangent z.1+
        R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) := by
    filter_upwards [hvgerm] with z hz
    exact congrArg (fun v => tangent z.1+v) hz
  have hangle := circular_angular_derivative
    ((hR.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₁.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₂.contDiffAt (O.isOpen.mem_nhds hJ)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hα.contDiffAt hnb).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
  funext i
  fin_cases i
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (l.leadingVelocity (J,t))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    exact hlgerm.eq_of_nhds
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (slot 2 J)) = _
    exact spaceCoordinates.apply_symm_apply _
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean (slot 6 J)) = _
    exact spaceCoordinates.apply_symm_apply _
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean
      (fderiv ℝ l.leadingVelocity (J,t) (D,0))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply]
    exact congrArg (fun L : (LowJet × ℝ) →L[ℝ] Vec => L (D,0)) hlgerm.fderiv_eq
  · change spaceCoordinates (JetVelocityCoordinates.toEuclidean
      (fderiv ℝ l.velocity (J,t) (0,1))) = _
    rw [JetVelocityCoordinates.toEuclidean,ContinuousLinearEquiv.apply_symm_apply,hvgerm.fderiv_eq]
    exact hangle

end SurfaceVelocityFamily.Loop
end ClosedSurfaceR4

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularProfilePullback
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pull back the circular profiles through the actual second-jet section.
The only derivative of the section that enters is its transverse derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.GeometryPreservation
open NormalFrame VelocityFrame RealModes
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem circularFamilyProfile_comp {φ : E → F} {Q X Y C e₁ e₂ : F → Vec}
    {R : F → ℝ} {α : F × ℝ → ℝ} {x : E} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ x) (hQ : DifferentiableAt ℝ Q (φ x))
    (hR : DifferentiableAt ℝ R (φ x)) (h₁ : DifferentiableAt ℝ e₁ (φ x))
    (h₂ : DifferentiableAt ℝ e₂ (φ x)) (hα : DifferentiableAt ℝ α (φ x,t)) (d : E) :
    circularFamilyProfile (Q ∘ φ) (X ∘ φ) (Y ∘ φ) (C ∘ φ) (R ∘ φ)
      (e₁ ∘ φ) (e₂ ∘ φ) (fun z => α (φ z.1,z.2)) d (x,t) =
    circularFamilyProfile Q X Y C R e₁ e₂ α (fderiv ℝ φ x d) (φ x,t) := by
  have hσ := (hφ.hasFDerivAt.comp (x,t)
    (hasFDerivAt_fst (𝕜 := ℝ) (p := (x,t)))).prodMk
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x,t)))
  have hβ : fderiv ℝ (fun z : E × ℝ => α (φ z.1,z.2)) (x,t) (0,1) =
      fderiv ℝ α (φ x,t) (0,1) := by
    simpa [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
      ContinuousLinearMap.snd] using
      congrArg (fun L : (E × ℝ) →L[ℝ] ℝ => L (0,1)) (hα.hasFDerivAt.comp (x,t) hσ).fderiv
  have hf := hasFDerivAt_fst (𝕜 := ℝ) (p := (φ x,t))
  have hV := (hQ.hasFDerivAt.comp (φ x,t) hf).add ((hR.hasFDerivAt.comp (φ x,t) hf).smul
    ((hα.hasFDerivAt.cos.smul (h₁.hasFDerivAt.comp (φ x,t) hf)).add
      (hα.hasFDerivAt.sin.smul (h₂.hasFDerivAt.comp (φ x,t) hf))))
  change HasFDerivAt (fun z : F × ℝ => Q z.1+
    R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) _ (φ x,t) at hV
  have hW :
      fderiv ℝ (fun z : E × ℝ => Q (φ z.1)+
        R (φ z.1) • direction (e₁ (φ z.1)) (e₂ (φ z.1)) (α (φ z.1,z.2))) (x,t) (d,0) =
      fderiv ℝ (fun z : F × ℝ => Q z.1+
        R z.1 • direction (e₁ z.1) (e₂ z.1) (α z)) (φ x,t) (fderiv ℝ φ x d,0) := by
    simpa [Function.comp_def,ContinuousLinearMap.comp_apply,ContinuousLinearMap.fst,
      ContinuousLinearMap.snd] using
      congrArg (fun L : (E × ℝ) →L[ℝ] Vec => L (d,0)) (hV.differentiableAt.hasFDerivAt.comp (x,t) hσ).fderiv
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · exact hW
  · change ((R ∘ φ) x * fderiv ℝ (fun z => α (φ z.1,z.2)) (x,t) (0,1)) • _ = _
    rw [hβ]
    rfl

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LeadingProfileStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform C3 stability of the leading profiles on a compact spatial set,
including every phase on the period circle. -/
noncomputable section
open Set
open scoped ContDiff Topology Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open JetPolynomial JetVelocityCoordinates GeometryPreservation CovarianceCorrector
open LocalPeriodicExpansion WeightedEstimates
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

lemma leadingProfileMap_uniform_near {K : Set LeadingProfileInput} (hK : IsCompact K)
    (hKO : ∀ J ∈ K, J.1.1 ∈ O) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ J ∈ K, ∀ H : LeadingProfileInput,
      ‖H-J‖ < δ → ‖l.leadingProfileMap H-l.leadingProfileMap J‖ < ε := by
  have hh := hK.uniformContinuousAt_of_continuousAt l.leadingProfileMap
    (fun J hJ => l.leadingProfileMap_continuousAt (hKO J hJ)) (Metric.dist_mem_uniformity hε)
  obtain ⟨δ,hδ,hclose⟩ := Metric.mem_uniformity_dist.mp hh
  refine ⟨δ,hδ,?_⟩
  intro J hJ H hHJ
  have hd : dist J H < δ := by simpa only [dist_eq_norm,norm_sub_rev] using hHJ
  simpa only [Set.mem_ofPred_eq,Prod.fst,Prod.snd,dist_eq_norm,norm_sub_rev] using hclose hd hJ

/-- The slow baseline may be replaced by the original map in all five
leading profiles, using only its unweighted C3 error. -/
theorem geometricLeadingProfile_stability {S : TopologicalSpace.Opens JetPolynomial.Base}
    {F : JetPolynomial.Base → JetPolynomial.Space} (hF : ContDiff ℝ ∞ F)
    (hFO : MapsTo (lowJet F) S O) {K : Set JetPolynomial.Base}
    (hK : IsCompact K) (hKS : K ⊆ S) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ G : JetPolynomial.Base → JetPolynomial.Space,
      ∀ hG : ContDiff ℝ ∞ G, ∀ hGO : MapsTo (lowJet G) S O,
      WeightedBound S 1 3 δ (fun p => G p-F p) → ∀ p ∈ K, ∀ t : Period,
        ‖l.geometricLeadingProfile G hG hGO p t-l.geometricLeadingProfile F hF hFO p t‖ < ε := by
  let B : JetPolynomial.Base × ℝ → LeadingProfileInput := fun z =>
    ((lowJet F z.1,z.2),lowDerivative F 1 z.1)
  have hD : Continuous (lowDerivative F 1) := by
    have hh : ContDiff ℝ ∞ (fun p => fderiv ℝ (lowJet F) p (coordinateVector 1)) :=
      ((lowJet_smooth hF).fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply contDiff_const
    have he : (fun p => fderiv ℝ (lowJet F) p (coordinateVector 1)) = lowDerivative F 1 :=
      funext (lowJet_derivative hF 1)
    rw [he] at hh
    exact hh.continuous
  have hB : Continuous B :=
    (((lowJet_smooth hF).continuous.comp continuous_fst).prodMk continuous_snd).prodMk
      (hD.comp continuous_fst)
  have hBK : IsCompact (B '' (K ×ˢ Icc (0 : ℝ) 1)) :=
    (hK.prod isCompact_Icc).image hB
  obtain ⟨r,hr,hclose⟩ := l.leadingProfileMap_uniform_near hBK
    (by rintro _ ⟨z,hz,rfl⟩; exact hFO (hKS hz.1)) ε hε
  refine ⟨r/2,half_pos hr,?_⟩
  intro G hG hGO hb p hp t
  have ht : t ∈ ((↑) : ℝ → Period) '' Icc (0 : ℝ) (0+1) := by
    rw [AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨s,hs,hst⟩ := ht
  have hinput := leadingInput_sub_bound S.isOpen hF hG (half_pos hr).le hb (hKS hp) s
  have hinput' : ‖(((lowJet G p,s),lowDerivative G 1 p) : LeadingProfileInput)-B (p,s)‖ < r :=
    hinput.trans_lt (half_lt_self hr)
  have he := hclose (B (p,s)) (mem_image_of_mem B ⟨hp,by simpa only [zero_add] using hs⟩)
    ((lowJet G p,s),lowDerivative G 1 p) hinput'
  rw [l.leadingProfileMap_geometry hG hGO (hKS hp) s] at he
  change ‖_ - l.leadingProfileMap ((lowJet F p,s),lowDerivative F 1 p)‖ < ε at he
  rw [l.leadingProfileMap_geometry hF hFO (hKS hp) s] at he
  simpa only [geometricLeadingProfile,hst] using he

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_CircularSectionProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Circular profiles of the actual original immersion, expressed through
its second jet and its transverse third derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open NormalFrame VelocityFrame RealModes JetPolynomial JetVelocityCoordinates GeometryPreservation
variable {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)

theorem circular_geometricLeadingProfile {R : LowJet → ℝ} {e₁ e₂ : LowJet → Vec}
    {α : LowJet × ℝ → ℝ} (hR : ContDiffOn ℝ ∞ R O)
    (h₁ : ContDiffOn ℝ ∞ e₁ O) (h₂ : ContDiffOn ℝ ∞ e₂ O)
    (hα : ContDiffOn ℝ ∞ α (O ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      R J • direction (e₁ J) (e₂ J) (α (J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G : JetPolynomial.Base → JetPolynomial.Space} (hG : ContDiff ℝ ∞ G)
    (hGO : MapsTo (lowJet G) S O) {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    boundaryProfileMap (l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period)) =
      circularFamilyProfile (tangent ∘ lowJet G) ((slot 1) ∘ lowJet G)
        ((slot 2) ∘ lowJet G) ((slot 6) ∘ lowJet G) (R ∘ lowJet G)
        (e₁ ∘ lowJet G) (e₂ ∘ lowJet G) (fun z => α (lowJet G z.1,z.2))
        (coordinateVector 1) (p,t) := by
  have hj := hGO hp
  have he : l.geometricLeadingProfile G hG hGO p (t : CovarianceCorrector.Period) =
      l.leadingProfileMap ((lowJet G p,t),lowDerivative G 1 p) :=
    (l.leadingProfileMap_geometry hG hGO hp t).symm
  rw [he,l.circular_leadingProfileMap hR h₁ h₂ hα hvel hj]
  have hQ : DifferentiableAt ℝ tangent (lowJet G p) :=
    (l.smoothTangent.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hh := circularFamilyProfile_comp (t := t) (X := slot 1) (Y := slot 2) (C := slot 6)
    ((lowJet_smooth hG).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p) hQ
    ((hR.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₁.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((h₂.contDiffAt (O.isOpen.mem_nhds hj)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    ((hα.contDiffAt ((O.isOpen.prod isOpen_univ).mem_nhds ⟨hj,mem_univ t⟩)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (coordinateVector 1)
  rw [lowJet_derivative hG] at hh
  exact hh.symm

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ActualCircularProfile
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The constructed real surface profile is exactly the analytic loop's
five-profile map, including its transverse mixed derivative. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation SurfaceJetCoordinates
open JetVelocityCoordinates

lemma actual_circular_geometric_profile {F : SmallModes.Base → Vec} (hF : ContDiff ℝ ∞ F)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (F ∘ baseEquiv)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : ℝ) :
    boundaryProfileMap (l.geometricLeadingProfile (F ∘ baseEquiv) (hF.comp baseEquiv.contDiff)
      hGO p (t : CovarianceCorrector.Period)) =
      surfaceCircularProfile F a e₁ e₂ α (baseEquiv p,t) := by
  let σ := JetPolynomial.lowJet (F ∘ baseEquiv)
  let R₀ : JetPolynomial.LowJet → ℝ := fun J => velocityRadius (normal J) (a (decode J).1)
  have hA : ContDiff ℝ ∞ (fun J : JetPolynomial.LowJet => a (decode J).1) :=
    ha.comp (contDiff_fst.comp decode_smooth)
  have hR₀ : ContDiffOn ℝ ∞ R₀ O := velocityRadius_smoothOn l.smoothNormal hA.contDiffOn (by
    intro J hJ
    have hh := l.nonzero J hJ
    rw [hamp J hJ] at hh
    exact hh)
  have he₁ := h₁.comp decode_smooth.contDiffOn hOZ
  have he₂ := h₂.comp decode_smooth.contDiffOn hOZ
  have hα₀ : ContDiffOn ℝ ∞ (fun z : JetPolynomial.LowJet × ℝ => α (decode z.1,z.2))
      (O ×ˢ univ) := hα.comp ((decode_smooth.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun _ hz => ⟨hOZ hz.1,hz.2⟩)
  rw [l.circular_geometricLeadingProfile hR₀ he₁ he₂ hα₀ hvel
    (hF.comp baseEquiv.contDiff) hGO hp t]
  let X := coordDeriv dx F
  let Y := coordDeriv dy F
  let C := coordDeriv dy (coordDeriv dy F)
  let v : SmallModes.Base → Vec := fun x => jetNormal (CollarVelocity.jetSection F x)
  let Q := X-v
  let R : SmallModes.Base → ℝ := fun x => velocityRadius (v x) (a x)
  let E₁ := e₁ ∘ CollarVelocity.jetSection F
  let E₂ := e₂ ∘ CollarVelocity.jetSection F
  let β : SmallModes.Base × ℝ → ℝ := fun z => α (CollarVelocity.jetSection F z.1,z.2)
  have hq : tangent ∘ σ = Q ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 0 - jetNormal (decode (σ x)) = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hx : (slot 1) ∘ σ = X ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 0 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hy : (slot 2) ∘ σ = Y ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 1 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hc : (slot 6) ∘ σ = C ∘ baseEquiv := by
    funext x
    change (decode (σ x)).2 4 = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have hr : R₀ ∘ σ = R ∘ baseEquiv := by
    funext x
    change velocityRadius (jetNormal (decode (σ x))) (a (decode (σ x)).1) = _
    rw [show decode (σ x) = CollarVelocity.jetSection F (baseEquiv x) from decode_lowJet hF x]
    rfl
  have he1 : (e₁ ∘ decode) ∘ σ = E₁ ∘ baseEquiv := by
    funext x
    exact congrArg e₁ (decode_lowJet hF x)
  have he2 : (e₂ ∘ decode) ∘ σ = E₂ ∘ baseEquiv := by
    funext x
    exact congrArg e₂ (decode_lowJet hF x)
  have hb : (fun z : JetPolynomial.Base × ℝ => α (decode (σ z.1),z.2)) =
      fun z => β (baseEquiv z.1,z.2) := by
    funext z
    rw [show decode (σ z.1) = CollarVelocity.jetSection F (baseEquiv z.1) from decode_lowJet hF z.1]
  change circularFamilyProfile (tangent ∘ σ) ((slot 1) ∘ σ) ((slot 2) ∘ σ) ((slot 6) ∘ σ)
    (R₀ ∘ σ) ((e₁ ∘ decode) ∘ σ) ((e₂ ∘ decode) ∘ σ)
    (fun z => α (decode (σ z.1),z.2)) (JetPolynomial.coordinateVector 1) (p,t) = _
  rw [hq,hx,hy,hc,hr,he1,he2,hb]
  have hJ := hGO hp
  have hZp : CollarVelocity.jetSection F (baseEquiv p) ∈ Z := by
    rw [← decode_lowJet hF p]
    exact hOZ hJ
  have hD : gramDet (Y (baseEquiv p)) (C (baseEquiv p)) ≠ 0 := by
    have hh := l.gram_ne _ hJ
    change gramDet ((decode (σ p)).2 1) ((decode (σ p)).2 4) ≠ 0 at hh
    rw [show decode (σ p) = CollarVelocity.jetSection F (baseEquiv p) from decode_lowJet hF p] at hh
    exact hh
  have hv : ContDiffAt ℝ ∞ v (baseEquiv p) :=
    contDiffAt_realNormalPart (contDiff_real_coordDeriv hF dy).contDiffAt
      (contDiff_real_coordDeriv (contDiff_real_coordDeriv hF dy) dy).contDiffAt
      (contDiff_real_coordDeriv hF dx).contDiffAt hD
  have hn : v (baseEquiv p) ≠ 0 ∨ a (baseEquiv p) ≠ 0 := by
    have hh := l.nonzero _ hJ
    rw [hamp _ hJ] at hh
    change jetNormal (decode (σ p)) ≠ 0 ∨ a (baseEquiv p) ≠ 0 at hh
    rw [show decode (σ p) = CollarVelocity.jetSection F (baseEquiv p) from decode_lowJet hF p] at hh
    exact hh
  have hdot : ContDiffAt ℝ ∞ (fun x => v x ⬝ᵥ v x) (baseEquiv p) :=
    ContDiffAt.sum (fun i _ => (contDiffAt_pi.mp hv i).mul (contDiffAt_pi.mp hv i))
  have hR : ContDiffAt ℝ ∞ R (baseEquiv p) :=
    (hdot.add (ha.contDiffAt.pow 2)).sqrt (Real.sqrt_pos.mp (velocityRadius_pos hn)).ne'
  have hσ := CollarVelocity.jetSection_smooth hF
  have hE1 := (h₁.contDiffAt (Z.isOpen.mem_nhds hZp)).comp _ hσ.contDiffAt
  have hE2 := (h₂.contDiffAt (Z.isOpen.mem_nhds hZp)).comp _ hσ.contDiffAt
  have hβ : ContDiffAt ℝ ∞ β (baseEquiv p,t) :=
    (hα.contDiffAt ((Z.isOpen.prod isOpen_univ).mem_nhds ⟨hZp,mem_univ t⟩)).comp _
      ((hσ.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  rw [circularFamilyProfile_comp (Q := Q) (X := X) (Y := Y) (C := C) (R := R)
    (e₁ := E₁) (e₂ := E₂) (α := β) baseEquiv.differentiableAt
    (((contDiff_real_coordDeriv hF dx).contDiffAt.sub hv).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hR.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hE1.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hE2.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hβ.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)),baseEquiv.fderiv]
  have hd : baseEquiv.toContinuousLinearMap (JetPolynomial.coordinateVector 1) = dy := baseEquiv_one
  rw [hd]
  rfl

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ActualCircularPeriod
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Representatives in one compact period transfer the constructed surface
profile estimates to the analytic loop at every phase. -/
noncomputable section
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.SurfaceVelocityFamily.Loop
open SmallModes RealModes VelocityFrame NormalFrame GeometryPreservation SurfaceJetCoordinates
open JetVelocityCoordinates

lemma actual_circular_period_profile {F : SmallModes.Base → Vec} (hF : ContDiff ℝ ∞ F)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → Vec} (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (F ∘ baseEquiv)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : CovarianceCorrector.Period) :
    ∃ s : ℝ, s ∈ Icc (0 : ℝ) 1 ∧
      boundaryProfileMap (l.geometricLeadingProfile (F ∘ baseEquiv) (hF.comp baseEquiv.contDiff)
        hGO p t) = surfaceCircularProfile F a e₁ e₂ α (baseEquiv p,s) := by
  have ht : t ∈ ((↑) : ℝ → CovarianceCorrector.Period) '' Icc (0 : ℝ) (0+1) := by
    rw [AddCircle.coe_image_Icc_eq]
    trivial
  obtain ⟨s,hs,hst⟩ := ht
  refine ⟨s,by simpa only [zero_add] using hs,?_⟩
  rw [← hst]
  exact l.actual_circular_geometric_profile hF ha hOZ hamp h₁ h₂ hα hvel hGO hp s

end ClosedSurfaceR4.SurfaceVelocityFamily.Loop

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PrimitiveProfileStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The five primitive derivative components are stable under a global C2
correction.  Their bound is uniform in the fast scale between zero and one. -/
noncomputable section
open Set
open scoped ContDiff

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial SurfaceVelocityFamily.Loop
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma vectorChartRead_sub (i : A.centers) (F G : M → Space) :
    A.vectorChartRead i (G-F) = A.vectorChartRead i G-A.vectorChartRead i F := by
  funext x
  unfold vectorChartRead localize
  by_cases hx : x ∈ (chart (i : M)).target <;> simp [hx,smul_sub]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_AtlasLeadingProfileStability
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global C3 displacement controls all five geometric leading profiles
in a fixed atlas chart, uniformly on compact sets and all periodic phases. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetVelocityCoordinates WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma jetChartMap_sub (i : A.centers) (F G : M → Space) :
    A.jetChartMap i (G-F) = fun p => A.jetChartMap i G p-A.jetChartMap i F p := by
  unfold jetChartMap
  rw [A.vectorChartRead_sub]
  funext p
  exact map_sub spaceCoordinates _ _

theorem jetChartMap_bound (i : A.centers) (m : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
      ∀ C : ℝ, 0 ≤ C → A.WeightedBound 1 m C F →
      WeightedEstimates.WeightedBound univ 1 m (D*C) (A.jetChartMap i F) := by
  obtain ⟨D,hD,hd⟩ := A.vectorChartRead_bound (V := Space) i m
  refine ⟨‖spaceCoordinates.toContinuousLinearMap‖*D,mul_nonneg (norm_nonneg _) hD,?_⟩
  intro F hF C hC hb
  have hh := (hd F 1 C zero_lt_one le_rfl hC hF hb).linear uniqueDiffOn_univ zero_le_one
    (A.vectorChartRead_smooth i hF).contDiffOn spaceCoordinates.toContinuousLinearMap
  simpa only [jetChartMap,Function.comp_def,mul_assoc,ContinuousLinearEquiv.coe_coe] using hh

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseLeadingProfileStability
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global C3 displacement controls all five geometric leading profiles
in a fixed atlas chart, uniformly on compact sets and all periodic phases. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetVelocityCoordinates WeightedEstimates
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

theorem phase_geometricLeadingProfile_stability (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hSc : IsCompact (closure (S : Set JetPolynomial.Base)))
    (hFO : MapsTo (lowJet (A.jetChartMap i F ∘ T)) S O) {K : Set JetPolynomial.Base}
    (hK : IsCompact K) (hKS : K ⊆ S) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ G : M → Space, ∀ hG : ContMDiff planeModel spaceModel ∞ G,
      ∀ hGO : MapsTo (lowJet (A.jetChartMap i G ∘ T)) S O,
      A.WeightedBound 1 3 ρ (G-F) → ∀ p ∈ K, ∀ t : CovarianceCorrector.Period,
      ‖l.geometricLeadingProfile (A.jetChartMap i G ∘ T) ((A.jetChartMap_smooth i hG).comp hT) hGO p t-
        l.geometricLeadingProfile (A.jetChartMap i F ∘ T) ((A.jetChartMap_smooth i hF).comp hT) hFO p t‖ < ε := by
  obtain ⟨δ,hδ,hclose⟩ := l.geometricLeadingProfile_stability
    ((A.jetChartMap_smooth i hF).comp hT) hFO hK hKS ε hε
  obtain ⟨D₀,hD₀,hd⟩ := A.jetChartMap_bound i 3
  obtain ⟨D₁,hD₁,hcomp⟩ := compact_composition_bound (E := JetPolynomial.Space) hT S.isOpen hSc 3
  let ρ := δ/(D₁*D₀+1)
  have hD : 0 ≤ D₁*D₀ := mul_nonneg (by linarith) hD₀
  have hρ : 0 < ρ := div_pos hδ (by positivity)
  refine ⟨ρ,hρ,?_⟩
  intro G hG hGO hb p hp t
  have hbound := hd (G-F) (hG.sub hF) ρ hρ.le hb
  have hc := hcomp (A.jetChartMap i (G-F)) (D₀*ρ)
    (mul_nonneg hD₀ hρ.le) (A.jetChartMap_smooth i (hG.sub hF)) hbound
  rw [A.jetChartMap_sub] at hc
  apply hclose _ ((A.jetChartMap_smooth i hG).comp hT) hGO _ p hp t
  apply hc.mono_const
  have he : ρ*(D₁*D₀+1) = δ := div_mul_cancel₀ δ (by positivity)
  nlinarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseBoundaryProfile
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Read the exact immersion's five profiles in the real coordinate chart
used by the Gauss and boundary calculations. -/
noncomputable section
open Set Manifold
open scoped ContDiff
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma phaseRealChartMap_smooth (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ContDiff ℝ ∞ (A.phaseRealChartMap i T F) :=
  (A.jetChartMap_smooth i hF).comp (hT.comp baseEquiv.symm.contDiff)

lemma phaseRealChartMap_profile (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (z : ℝ) (p : JetPolynomial.Base) :
    boundaryProfileMap (SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F ∘ T) z p) =
      realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p) := by
  have he : (fun q => JetVelocityCoordinates.toEuclidean (A.phaseRealChartMap i T F (baseEquiv q))) =
      A.vectorChartRead i F ∘ T := by
    funext q
    change spaceCoordinates.symm
      (A.jetChartMap i F (T (baseEquiv.symm (baseEquiv q)))) = A.vectorChartRead i F (T q)
    rw [baseEquiv.symm_apply_apply]
    exact spaceCoordinates.symm_apply_apply _
  simpa only [he] using boundaryProfileMap_chart (A.phaseRealChartMap_smooth i hT hF) z p

/-- The exact primitive's Euclidean profile estimate gives the real-coordinate
estimate used by the boundary preservation lemmas. -/
lemma phaseRealChartMap_profile_error (i : A.centers)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F) (z : ℝ) (p : JetPolynomial.Base)
    (J : EuclideanBoundaryProfile) {ε : ℝ} (hε : 0 < ε)
    (hclose : ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F ∘ T) z p - J‖ <
      ε / (‖boundaryProfileMap‖ + 1)) :
    ‖realBoundaryProfile (A.phaseRealChartMap i T F) z (baseEquiv p) - boundaryProfileMap J‖ < ε := by
  rw [← A.phaseRealChartMap_profile i hT hF z p, ← map_sub]
  calc
    ‖boundaryProfileMap _‖ ≤ ‖boundaryProfileMap‖ *
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A.vectorChartRead i F ∘ T) z p - J‖ :=
      boundaryProfileMap.le_opNorm _
    _ < (‖boundaryProfileMap‖ + 1) * (ε / (‖boundaryProfileMap‖ + 1)) := by
      have hn := norm_nonneg boundaryProfileMap
      have hd : 0 < ‖boundaryProfileMap‖ + 1 := by positivity
      have he : 0 < ε / (‖boundaryProfileMap‖ + 1) := div_pos hε hd
      nlinarith [mul_le_mul_of_nonneg_left hclose.le hn]
    _ = ε := mul_div_cancel₀ ε (by positivity)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentExactOriginalProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentExactPhaseOriginalProfilesDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentExactPhaseOriginalProfilesFiberSpace
local instance independentExactPhaseOriginalProfilesDualSmul_rd39f63_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independentExactPhaseOriginalProfilesFiberNormed
local instance independentExactPhaseOriginalProfilesSectionNormed_rd39f63_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independentExactPhaseOriginalProfilesSectionSpace_rd39f63_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_exact_phase_primitive_original_profiles [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
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

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C,
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A₀.vectorChartRead i W ∘ e.symm) z p-
          l.geometricLeadingProfile (A₀.jetChartMap i F ∘ e.symm) ((A₀.jetChartMap_smooth i hF).comp hi)
            (fun _ hp => hQO (hFQ hp)) p ((ℓ p/z : ℝ) : Period)‖ < ε) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  have hall := data.independent_exact_phase_primitive_five_profiles A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
    l ha hamp S hSc hTS hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy h htarget
  intro ε hε ζ hζ
  obtain ⟨ρ,hρ,hstable⟩ := A₀.phase_geometricLeadingProfile_stability i hF hi l hSc
    (fun _ hp => hQO (hFQ hp)) hC (fun _ hp => (hCS hp).1) (ε/2) (half_pos hε)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hgeometry,G,hG,hGO,hslow,hprofile,V,hV,hcorrection,hexterior⟩ :=
    hall (min (ε/2) ρ) (lt_min (half_pos hε) hρ) ζ hζ
  have hslowρ : A₀.WeightedBound 1 3 ρ (G-F) :=
    fun j => (hslow j).mono_const (min_le_right _ _)
  refine ⟨z,hz,hzζ,hz1,W,hW,hgeometry,?_,G,hG,?_,V,hV,hcorrection,hexterior⟩
  · intro p hp
    have hfirst :
        ‖SurfaceVelocityFamily.Loop.primitiveJetProfile (A₀.vectorChartRead i W ∘ e.symm) z p-
          l.geometricLeadingProfile (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi)
            hGO p ((ℓ p/z : ℝ) : Period)‖ ≤ ε/2 :=
      (hprofile p (hCS hp)).trans (min_le_left _ _)
    have hsecond := hstable G hG hGO hslowρ p hp ((ℓ p/z : ℝ) : Period)
    have htriangle := dist_triangle
      (SurfaceVelocityFamily.Loop.primitiveJetProfile (A₀.vectorChartRead i W ∘ e.symm) z p)
      (l.geometricLeadingProfile (A₀.jetChartMap i G ∘ e.symm) ((A₀.jetChartMap_smooth i hG).comp hi)
        hGO p ((ℓ p/z : ℝ) : Period))
      (l.geometricLeadingProfile (A₀.jetChartMap i F ∘ e.symm) ((A₀.jetChartMap_smooth i hF).comp hi)
        (fun _ hp => hQO (hFQ hp)) p ((ℓ p/z : ℝ) : Period))
    simp only [dist_eq_norm] at htriangle
    linarith
  · exact fun j => (hslow j).mono_const ((min_le_left _ _).trans (by linarith))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentPhaseBoundaryProfiles
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactPhaseBoundaryProfilesDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactPhaseBoundaryProfilesFiberSpace
local instance independent_exactPhaseBoundaryProfilesDualSmul_rd39f63_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactPhaseBoundaryProfilesFiberNormed
local instance independent_exactPhaseBoundaryProfilesSectionNormed_rd39f63_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_exactPhaseBoundaryProfilesSectionSpace_rd39f63_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_exact_phase_primitive_boundary_profiles [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
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

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![a q^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C,
        ‖realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (SurfaceJetCoordinates.baseEquiv p)-
          boundaryProfileMap (l.geometricLeadingProfile (A₀.jetChartMap i F ∘ e.symm)
            ((A₀.jetChartMap_smooth i hF).comp hi)
            (fun _ hp => hQO (hFQ hp)) p ((ℓ p/z : ℝ) : Period))‖ < ε) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  have hall := data.independent_exact_phase_primitive_original_profiles A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
    l ha hamp S hSc hTS hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy h htarget hC hCS
  intro ε hε ζ hζ
  let δ := ε/(‖boundaryProfileMap‖+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨z,hz,hzζ,hz1,W,hW,hgeometry,hprofiles,G,hG,hslow,V,hV,hcorrection,hext⟩ :=
    hall δ hδ ζ hζ
  refine ⟨z,hz,hzζ,hz1,W,hW,hgeometry,?_,G,hG,?_,V,hV,hcorrection,hext⟩
  · intro p hp
    exact A₀.phaseRealChartMap_profile_error i hi hW.1 z p _ hε (hprofiles p hp)
  · exact fun j => (hslow j).mono_const (div_le_self hε.le (by linarith [norm_nonneg boundaryProfileMap]))

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PhaseCircularPeriod
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The analytic profile attached to an atlas phase chart is exactly one
of the real circular profiles used in the finite boundary construction. -/
noncomputable section
open Set Manifold
open scoped ContDiff Topology Manifold
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open RealModes SurfaceJetCoordinates GeometryPreservation SurfaceVelocityFamily VelocityFrame
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

omit [CompactSpace M] in
lemma phaseRealChartMap_comp_base (i : A.centers) (T : JetPolynomial.Base → JetPolynomial.Base)
    (F : M → Space) : A.phaseRealChartMap i T F ∘ baseEquiv = A.jetChartMap i F ∘ T := by
  funext p
  simp only [Function.comp_apply,phaseRealChartMap,baseEquiv.symm_apply_apply]

private lemma geometric_profile_congr {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (l : _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop O) {S : TopologicalSpace.Opens JetPolynomial.Base}
    {G H : JetPolynomial.Base → JetPolynomial.Space} (he : G = H)
    (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hGO : MapsTo (JetPolynomial.lowJet G) S O) (hHO : MapsTo (JetPolynomial.lowJet H) S O)
    (p : JetPolynomial.Base) (t : CovarianceCorrector.Period) :
    l.geometricLeadingProfile G hG hGO p t = l.geometricLeadingProfile H hH hHO p t := by
  subst H
  rfl


lemma phase_circular_period_profile (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    {T : JetPolynomial.Base → JetPolynomial.Base} (hT : ContDiff ℝ ∞ T)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {Z : TopologicalSpace.Opens GeometricJet} {O : TopologicalSpace.Opens JetPolynomial.LowJet}
    (hOZ : (O : Set JetPolynomial.LowJet) ⊆ jetDomain Z) (l : _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop O)
    (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {e₁ e₂ : GeometricJet → NormalFrame.Vec}
    (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
    {S : TopologicalSpace.Opens JetPolynomial.Base}
    (hGO : MapsTo (JetPolynomial.lowJet (A.jetChartMap i F ∘ T)) S O)
    {p : JetPolynomial.Base} (hp : p ∈ S) (t : CovarianceCorrector.Period) :
    ∃ s : ℝ, s ∈ Icc (0 : ℝ) 1 ∧
      boundaryProfileMap (l.geometricLeadingProfile (A.jetChartMap i F ∘ T)
        ((A.jetChartMap_smooth i hF).comp hT) hGO p t) =
      surfaceCircularProfile (A.phaseRealChartMap i T F) a e₁ e₂ α (baseEquiv p,s) := by
  have hcomp := A.phaseRealChartMap_comp_base i T F
  have hGO' : MapsTo (JetPolynomial.lowJet (A.phaseRealChartMap i T F ∘ baseEquiv)) S O := by
    simpa only [hcomp] using hGO
  obtain ⟨s,hs,he⟩ := l.actual_circular_period_profile (A.phaseRealChartMap_smooth i hT hF)
    ha hOZ hamp h₁ h₂ hα hvel hGO' hp t
  have heq := geometric_profile_congr l hcomp
    ((A.phaseRealChartMap_smooth i hT hF).comp baseEquiv.contDiff)
    ((A.jetChartMap_smooth i hF).comp hT) hGO' hGO p t
  exact ⟨s,hs,(congrArg boundaryProfileMap heq).symm.trans he⟩

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_IndependentExactCircular
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual finite-accuracy primitive immersions with a Riemannian target,
uniform first-jet bounds, and a uniform nonzero second-form margin. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation RealModes CovarianceCorrector GeometryPreservation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
open SurfaceJetCoordinates SurfaceVelocityFamily VelocityFrame
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveFiberSpace
local instance independent_exactCircularPrimitiveDualSmul_rd39f63_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.independent_exactCircularPrimitiveFiberNormed
local instance independent_exactCircularPrimitiveSectionNormed_rd39f63_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance independent_exactCircularPrimitiveSectionSpace_rd39f63_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem independent_exact_circular_primitive_profiles_oai [T2Space M] (data : MetricGoodPhaseData g F) (A₀ : SmoothingAtlas M)
    (houter : ∀ i x, x ∈ tsupport (A₀.weight i) → A₀.outer i =ᶠ[𝓝 x] (fun _ => 1))
    (hF : ContMDiff planeModel spaceModel ∞ F) (hmetric : g.inner = inducedTensor F)
    (i : A₀.centers)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχs : tsupport χ ⊆ e.source)
    (hcover : (A₀.chartWeightCompact i : Set JetPolynomial.Base) ⊆ e.source)
    {O : TopologicalSpace.Opens LowJet} (l : SurfaceVelocityFamily.Loop O)
    {a : SmallModes.Base → ℝ} (ha : ContDiff ℝ ∞ a) (hamp : l.HasSpatialAmplitude (a ∘ baseEquiv))
    {Z : TopologicalSpace.Opens GeometricJet} (hOZ : (O : Set LowJet) ⊆ jetDomain Z)
    {e₁ e₂ : GeometricJet → NormalFrame.Vec}
    (h₁ : ContDiffOn ℝ ∞ e₁ Z) (h₂ : ContDiffOn ℝ ∞ e₂ Z)
    {α : GeometricJet × ℝ → ℝ} (hα : ContDiffOn ℝ ∞ α (Z ×ˢ univ))
    (hvel : ∀ J ∈ O, ∀ t, l.velocity (J,t) =
      velocityRadius (normal J) (a (decode J).1) •
        VelocityFrame.direction (e₁ (decode J)) (e₂ (decode J)) (α (decode J,t)))
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

    (h : SmoothMetric M)
    (htarget : h.inner = g.inner + A₀.bundleRestore A₀.tensorTriv i
      (fun y => fiberFromThree (localizedTensorPullback e χ (fun q => ![(a (baseEquiv q))^2,0,0]) y)))
    {C : Set JetPolynomial.Base} (hC : IsCompact C)
    (hCS : C ⊆ (S : Set JetPolynomial.Base) ∩ e.target) :
    ∀ ε : ℝ, 0 < ε → ∀ ζ : ℝ, 0 < ζ →
    ∃ z : ℝ, 0 < z ∧ z < ζ ∧ z ≤ 1 ∧ ∃ W : M → Space,
      IsSmoothIsometricImmersion M h W ∧ Nonempty (MetricGoodPhaseData h W) ∧
      (∀ p ∈ C, ∃ t : ℝ, t ∈ Icc (0 : ℝ) 1 ∧
        ‖realBoundaryProfile (A₀.phaseRealChartMap i e.symm W) z (baseEquiv p)-
          surfaceCircularProfile (A₀.phaseRealChartMap i e.symm F) a e₁ e₂ α (baseEquiv p,t)‖ < ε) ∧
      ∃ G : M → Space, ∃ _hG : ContMDiff planeModel spaceModel ∞ G,
        A₀.WeightedBound 1 3 ε (G-F) ∧
        ∃ V : M → Space, ContMDiff planeModel spaceModel ∞ V ∧
          A₀.WeightedBound 1 2 (z^8) (W-V) ∧
          (∀ p ∉ tsupport (A₀.weight i), V =ᶠ[𝓝 p] G) ∧
        ∀ p ∉ A₀.phaseSurfaceSupport i e K, V =ᶠ[𝓝 p] G := by
  intro ε hε ζ hζ
  obtain ⟨z,hz,hzζ,hz1,W,hW,hgeometry,hprofiles,G,hG,hslow,V,hV,hcorrection,hext⟩ :=
    data.independent_exact_phase_primitive_boundary_profiles A₀ houter hF hmetric i e he hi hχ hχc hχs hcover
      l (ha.comp baseEquiv.contDiff) hamp S hSc hTS hQ hQO hFQ K hK hKS hKA hone hv ℓ hℓx hℓy
      h htarget hC hCS ε hε ζ hζ
  refine ⟨z,hz,hzζ,hz1,W,hW,hgeometry,?_,G,hG,hslow,V,hV,hcorrection,hext⟩
  intro p hp
  obtain ⟨t,ht,heq⟩ := A₀.phase_circular_period_profile i hF hi ha hOZ l hamp h₁ h₂ hα hvel
    (fun _ hp => hQO (hFQ hp)) (hCS hp).1 ((ℓ p/z : ℝ) : Period)
  refine ⟨t,ht,?_⟩
  rw [← heq]
  exact hprofiles p hp

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.independent_exact_circular_primitive_profiles_oai.{u_1}
