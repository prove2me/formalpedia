-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:42:26.373607+00:00
-- url     : https://prove2.me/submissions/087ba6c4-9fb5-4445-8aea-9a33d3da1f33

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
import Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_supported_local_metric_defect

section
-- module Solutions.OAIQ249_SI.Immersion_ClosedSurface_TensorCoordinates
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
open ClosedSurfaceR4.SmallModes ClosedSurfaceR4.WeightedEstimates
open ClosedSurfaceR4.PhaseMean



lemma realMetricTensor_comp {n : ℕ} {F : RField n} {χ : Base → Base} {p : Base}
    (hF : DifferentiableAt ℝ F (χ p)) (hχ : DifferentiableAt ℝ χ p) :
    realMetricTensor (F ∘ χ) p = pullbackField χ p (realMetricTensor F (χ p)) := by
  ext i
  rw [realMetricTensor_apply]
  change realMetric (F ∘ χ) (firstDirection i) (secondDirection i) p =
    evaluate (realMetricTensor F (χ p))
      (fderiv ℝ χ p (firstDirection i)) (fderiv ℝ χ p (secondDirection i))
  rw [evaluate_realMetricTensor]
  simp only [realMetric, coordDeriv, fderiv_comp p hF hχ, ContinuousLinearMap.comp_apply]

end ClosedSurfaceR4.RealModes

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

lemma jet_cons (G : Base → Space) (v : Fin 2) (w : List (Fin 2)) (a : Fin 4) (p : Base) :
    jet G (v :: w) a p = fderiv ℝ (jet G w a) p (coordinateVector v) := rfl

lemma lowJet_derivative {G : Base → Space} (hG : ContDiff ℝ ∞ G) (v : Fin 2) (p : Base) :
    fderiv ℝ (lowJet G) p (coordinateVector v) = lowDerivative G v p := by
  ext i
  have h := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
    (fderiv_apply ((lowJet_smooth hG).differentiable (by simp) p) i)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    lowJet_coordinate_derivative] using h.symm

lemma lowBasis_expansion (J : LowJet) : J = ∑ i : LowIndex, J i • lowBasis i := by
  ext i
  simp [lowBasis, Pi.single_apply]

/-- Differentiating a low-jet coefficient introduces only the next coordinate
jet, linearly, with new smooth low-jet coefficients. -/
theorem coefficient_chain_rule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {c : LowJet → E}
    (v : Fin 2) (p : Base) (hc : DifferentiableAt ℝ c (lowJet G p)) :
    fderiv ℝ (fun q => c (lowJet G q)) p (coordinateVector v) =
      ∑ i : LowIndex, (lowDerivative G v p i) • fderiv ℝ c (lowJet G p) (lowBasis i) := by
  have hQ := (lowJet_smooth hG).differentiable (by simp) p
  change fderiv ℝ (c ∘ lowJet G) p (coordinateVector v) = _
  rw [fderiv_comp p hc hQ, ContinuousLinearMap.comp_apply, lowJet_derivative hG]
  conv_lhs => rw [lowBasis_expansion (lowDerivative G v p), map_sum]
  simp only [map_smul]

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

lemma eval_mapCoeff_mul (e : Expression) (G : Base → Space) (c : LowJet × ℝ → ℝ)
    (z : Base × ℝ) :
    (e.mapCoeff (fun d x => c x * d x)).eval G z = c (lowJet G z.1, z.2) * e.eval G z := by
  induction e with
  | coeff d => rfl
  | atom w a e ih => simp only [mapCoeff, eval, ih] <;> ring
  | add e f ihe ihf => simp only [mapCoeff, eval, ihe, ihf] <;> ring

lemma eval_mul (e f : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.mul f).eval G z = e.eval G z * f.eval G z := by
  induction e with
  | coeff c => exact eval_mapCoeff_mul f G c z
  | atom w a e ih => simp only [mul, eval, ih] <;> ring
  | add e g ihe ihg => simp only [mul, eval, ihe, ihg] <;> ring

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LowJetCoordinateChange
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

private lemma coordinateVector_expansion (v : Base) :
    v = ∑ i : Fin 2, v i • coordinateVector i := by
  ext i
  simp [coordinateVector,Pi.single_apply]

private lemma coordinatePartial_component {T : Base → Base} (hT : ContDiff ℝ ∞ T)
    (v i : Fin 2) (x : Base) :
    coordinatePartial (fun y => T y i) v x = (fderiv ℝ T x (coordinateVector v)) i := by
  have h := congrArg (fun L : Base →L[ℝ] ℝ => L (coordinateVector v))
    (fderiv_apply (hT.differentiable (by simp) x) i)
  simpa only [coordinatePartial,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply] using h

lemma coordinatePartial_comp {f : Base → ℝ} {T : Base → Base}
    (hf : ContDiff ℝ ∞ f) (hT : ContDiff ℝ ∞ T) (v : Fin 2) (x : Base) :
    coordinatePartial (f ∘ T) v x =
      ∑ i : Fin 2, coordinatePartial (fun y => T y i) v x * coordinatePartial f i (T x) := by
  change fderiv ℝ (f ∘ T) x (coordinateVector v) = _
  rw [fderiv_comp x (hf.differentiable (by simp) _) (hT.differentiable (by simp) _),
    ContinuousLinearMap.comp_apply]
  conv_lhs => arg 2; rw [coordinateVector_expansion (fderiv ℝ T x (coordinateVector v))]
  rw [map_sum]
  simp only [map_smul,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [coordinatePartial_component hT]
  rfl

lemma coordinatePartial_coordinatePartial_comp {f : Base → ℝ} {T : Base → Base}
    (hf : ContDiff ℝ ∞ f) (hT : ContDiff ℝ ∞ T) (v w : Fin 2) (x : Base) :
    coordinatePartial (coordinatePartial (f ∘ T) w) v x =
      ∑ i : Fin 2,
        (coordinatePartial (fun y => T y i) w x *
          (∑ j : Fin 2, coordinatePartial (fun y => T y j) v x *
            coordinatePartial (coordinatePartial f i) j (T x)) +
        coordinatePartial (coordinatePartial (fun y => T y i) w) v x *
          coordinatePartial f i (T x)) := by
  have he : coordinatePartial (f ∘ T) w = fun y =>
      ∑ i : Fin 2, coordinatePartial (fun z => T z i) w y * coordinatePartial f i (T y) :=
    funext (coordinatePartial_comp hf hT w)
  have hTi (i : Fin 2) : ContDiff ℝ ∞ (coordinatePartial (fun y => T y i) w) :=
    coordinatePartial_smooth (contDiff_pi.mp hT i) w
  have hfi (i : Fin 2) : ContDiff ℝ ∞ (fun y => coordinatePartial f i (T y)) :=
    (coordinatePartial_smooth hf i).comp hT
  change fderiv ℝ (coordinatePartial (f ∘ T) w) x (coordinateVector v) = _
  rw [he,fderiv_fun_sum (fun i _ => ((hTi i).mul (hfi i)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_mul ((hTi i).differentiable (by simp) x) ((hfi i).differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  change coordinatePartial (fun y => T y i) w x *
      coordinatePartial (coordinatePartial f i ∘ T) v x +
      coordinatePartial f i (T x) *
        coordinatePartial (coordinatePartial (fun y => T y i) w) v x = _
  rw [coordinatePartial_comp (coordinatePartial_smooth hf i) hT]
  ring

lemma lowJet_first_slot (G : Base → Space) (v : Fin 2) (a : Fin 4) (x : Base) :
    lowJet G x (.inr (firstJetSlot v,a)) = coordinatePartial (fun y => G y a) v x := by
  fin_cases v <;> rfl

lemma lowJet_second_slot (G : Base → Space) (v w : Fin 2) (a : Fin 4) (x : Base) :
    lowJet G x (.inr (secondJetSlot v w,a)) =
      coordinatePartial (coordinatePartial (fun y => G y a) w) v x := by
  fin_cases v <;> fin_cases w <;> rfl

/-- The finite-dimensional transport agrees exactly with the low jet of
the composed smooth map. -/
theorem lowJetCoordinateChange_eval {G : Base → Space} {T : Base → Base}
    (hG : ContDiff ℝ ∞ G) (hT : ContDiff ℝ ∞ T) (x : Base) :
    lowJetCoordinateChange T (x,lowJet G (T x)) = lowJet (G ∘ T) x := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    rcases i with ⟨w,a⟩
    have hfirst (v : Fin 2) : coordinateChangeFirst T x (lowJet G (T x)) v a =
        coordinatePartial ((fun y => G y a) ∘ T) v x := by
      rw [coordinatePartial_comp (contDiff_pi.mp hG a) hT]
      simp only [coordinateChangeFirst,lowJet_first_slot]
    have hsecond (v w : Fin 2) : coordinateChangeSecond T x (lowJet G (T x)) v w a =
        coordinatePartial (coordinatePartial ((fun y => G y a) ∘ T) w) v x := by
      rw [coordinatePartial_coordinatePartial_comp (contDiff_pi.mp hG a) hT]
      simp only [coordinateChangeSecond,lowJet_first_slot,lowJet_second_slot]
    fin_cases w
    · rfl
    · exact hfirst 0
    · exact hfirst 1
    · exact hsecond 0 0
    · exact hsecond 0 1
    · exact hsecond 1 0
    · exact hsecond 1 1


private lemma iteratedDirectional_eventuallyEq {f g : Base → ℝ} {x : Base}
    (h : f =ᶠ[𝓝 x] g) (vs : List Base) :
    WeightedEstimates.iteratedDirectional vs f =ᶠ[𝓝 x]
      WeightedEstimates.iteratedDirectional vs g := by
  induction vs with
  | nil => exact h
  | cons v vs ih =>
    filter_upwards [ih.fderiv (𝕜 := ℝ)] with y hy
    exact congrArg (fun L : Base →L[ℝ] ℝ => L v) hy

/-- Positional jets only depend on the germ of the map. -/
lemma lowJet_eventuallyEq {G H : Base → Space} {x : Base}
    (h : G =ᶠ[𝓝 x] H) : lowJet G x = lowJet H x := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    have ha : (fun y => G y i.2) =ᶠ[𝓝 x] (fun y => H y i.2) :=
      h.mono (fun _ he => congrFun he i.2)
    exact (iteratedDirectional_eventuallyEq ha ((lowWord i.1).map coordinateVector)).self_of_nhds

/-- Evaluate the inverse-coordinate transport at `T x`. The only map
identification required here is the actual local germ `H ∘ S = G`. -/
lemma lowJetCoordinateChange_inverse_eval {G H : Base → Space} {T S : Base → Base}
    (hH : ContDiff ℝ ∞ H) (hS : ContDiff ℝ ∞ S) (x : Base)
    (hST : S (T x) = x) (hrel : (H ∘ S) =ᶠ[𝓝 (T x)] G) :
    lowJetCoordinateChange S (T x,lowJet H x) = lowJet G (T x) := by
  have h := lowJetCoordinateChange_eval hH hS (T x)
  rw [hST] at h
  exact h.trans (lowJet_eventuallyEq hrel)

/-- A local inverse and the local relation `H = G ∘ T` supply the germ in
`lowJetCoordinateChange_inverse_eval`. -/
lemma lowJetCoordinateChange_local_inverse {G H : Base → Space} {T S : Base → Base}
    (hH : ContDiff ℝ ∞ H) (hS : ContDiff ℝ ∞ S) (x : Base)
    (hST : S (T x) = x) (hTS : (T ∘ S) =ᶠ[𝓝 (T x)] id)
    (hrel : H =ᶠ[𝓝 x] (G ∘ T)) :
    lowJetCoordinateChange S (T x,lowJet H x) = lowJet G (T x) := by
  apply lowJetCoordinateChange_inverse_eval hH hS x hST
  have ht : Filter.Tendsto S (𝓝 (T x)) (𝓝 x) := by
    have hc : ContinuousAt S (T x) := hS.continuous.continuousAt
    change Filter.Tendsto S (𝓝 (T x)) (𝓝 (S (T x))) at hc
    rw [hST] at hc
    exact hc
  filter_upwards [hrel.comp_tendsto ht,hTS] with y hy hz
  change H (S y) = G y
  change H (S y) = G (T (S y)) at hy
  change T (S y) = y at hz
  simpa only [hz] using hy

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialDerivative
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma eval_sumList {ι : Type*} (l : List ι) (f : ι → Expression) (G : Base → Space)
    (z : Base × ℝ) : (sumList l f).eval G z = (l.map (fun i => (f i).eval G z)).sum := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [sumList, eval, List.map_cons, List.sum_cons, ih]

lemma smoothCoeffs_sumList {ι : Type*} {O : Set LowJet} (l : List ι) (f : ι → Expression)
    (hf : ∀ i ∈ l, (f i).SmoothCoeffs O) : (sumList l f).SmoothCoeffs O := by
  induction l with
  | nil => exact contDiffOn_const
  | cons i l ih => exact ⟨hf i (List.mem_cons_self ..),
      ih (fun j hj => hf j (List.mem_cons_of_mem _ hj))⟩

lemma eval_lowFactor (v : Fin 2) (i : LowIndex) (G : Base → Space) (z : Base × ℝ) :
    (lowFactor v i).eval G z = lowDerivative G v z.1 i := by
  cases i with
  | inl i => rfl
  | inr i => simp [lowFactor, eval, lowDerivative]

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

lemma coefficient_chain_rule_joint {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) {c : LowJet × ℝ → ℝ}
    (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)) (v : Fin 2) (p : Base)
    (hp : lowJet G p ∈ O) (t : ℝ) :
    fderiv ℝ (fun q => c (lowJet G q, t)) p (coordinateVector v) =
      ∑ i : LowIndex, lowDerivative G v p i * slowDerivative c (lowBasis i) (lowJet G p, t) := by
  have hs : DifferentiableAt ℝ (fun Q : LowJet => c (Q, t)) (lowJet G p) :=
    ((hc.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp _
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  simpa only [smul_eq_mul, LocalPeriodicCalculus.fderiv_slice hO hc hp] using
    coefficient_chain_rule hG v p hs

/-- The syntactic derivative evaluates to the genuine derivative on every
open region where the low-jet coefficients are smooth. -/
theorem eval_slow {O : Set LowJet} {S : Set Base} (hO : IsOpen O) (hS : IsOpen S)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (v : Fin 2) {e : Expression} (he : e.SmoothCoeffs O) {p : Base} (hp : p ∈ S) (t : ℝ) :
    (e.slow v).eval G (p, t) = fderiv ℝ (fun q => e.eval G (q, t)) p (coordinateVector v) := by
  induction e with
  | coeff c =>
    rw [slow, eval_sumList, ← List.sum_toFinset _ Finset.univ.nodup_toList,
      Finset.toList_toFinset]
    simp only [eval_mul, eval_lowFactor, eval]
    exact (coefficient_chain_rule_joint hO hG he v p (hQ hp) t).symm
  | atom w a e ih =>
    have hj := (jet_smooth hG w a).differentiable (by simp) p
    have he' : DifferentiableAt ℝ (fun q => e.eval G (q, t)) p :=
      (((eval_smooth hG hQ (e := e) he).contDiffAt
        ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simp only [slow, eval, ih he]
    rw [fderiv_fun_mul hj he']
    simp only [add_apply, smul_apply, smul_eq_mul,
      jet_cons]
    ring
  | add e f ihe ihf =>
    have hd (g : Expression) (hg : g.SmoothCoeffs O) :
        DifferentiableAt ℝ (fun q => g.eval G (q, t)) p :=
      (((eval_smooth hG hQ hg).contDiffAt
        ((hS.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [slow, eval, fderiv_fun_add (hd e he.1) (hd f he.2),
      add_apply] using congrArg₂ (· + ·) (ihe he.1) (ihf he.2)

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_JetPullbackExpressions
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_angle _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_mean _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_primitive _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma coordinate_basis_expansion (v : Base) :
    (∑ k : Fin 2, v k • coordinateVector k) = v := by
  ext i
  simp [coordinateVector,Pi.single_apply]

/-- The polynomial is the actual ordered coordinate derivative in the
other chart. The inverse differential condition is local and exact. -/
theorem jetPullback_eval {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hinv : ∀ x ∈ U, (fderiv ℝ T x).comp (fderiv ℝ S (T x)) = ContinuousLinearMap.id ℝ Base)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (w : List (Fin 2)) (a : Fin 4) (t : ℝ) :
    ∀ x ∈ U, (jetPullback T S w a).eval H (x,t) = jet G w a (T x) := by
  induction w with
  | nil =>
    intro x hx
    change H x a = G (T x) a
    exact congrFun (hrel x hx) a
  | cons i w ih =>
    intro x hx
    have heq : (fun y => (jetPullback T S w a).eval H (y,t)) =ᶠ[𝓝 x]
        (fun y => jet G w a (T y)) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact ih y hy
    have hs := jet_smooth hG w a
    have hd : fderiv ℝ (fun y => (jetPullback T S w a).eval H (y,t)) x =
        (fderiv ℝ (jet G w a) (T x)).comp (fderiv ℝ T x) := by
      rw [heq.fderiv_eq]
      exact fderiv_comp x (hs.differentiable (by simp) _) (hT.differentiable (by simp) x)
    rw [jetPullback,Expression.eval_sumList,← List.sum_toFinset _ Finset.univ.nodup_toList,
      Finset.toList_toFinset]
    simp only [Expression.eval_mul,Expression.eval,inverseCoordinateCoefficient,lowPosition_lowJet]
    simp_rw [Expression.eval_slow isOpen_univ hU hH (mapsTo_univ _ _) _
      (jetPullback_smooth hT hS w a) hx,hd,ContinuousLinearMap.comp_apply]
    have hsum : (∑ k : Fin 2, (fderiv ℝ S (T x) (coordinateVector i)) k *
        fderiv ℝ (jet G w a) (T x) (fderiv ℝ T x (coordinateVector k))) =
        fderiv ℝ (jet G w a) (T x)
          (fderiv ℝ T x (fderiv ℝ S (T x) (coordinateVector i))) := by
      conv_rhs => rw [← coordinate_basis_expansion (fderiv ℝ S (T x) (coordinateVector i))]
      simp only [map_sum,map_smul,smul_eq_mul]
    rw [hsum]
    have hi := congrArg (fun L : Base →L[ℝ] Base => L (coordinateVector i)) (hinv x hx)
    rw [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] at hi
    rw [hi]
    rfl


namespace Expression

lemma coordinatePullback_eval {T S : Base → Base} {K : LowJet → LowJet}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hinv : ∀ x ∈ U, (fderiv ℝ T x).comp (fderiv ℝ S (T x)) = ContinuousLinearMap.id ℝ Base)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (hjet : ∀ x ∈ U, lowJet G (T x) = K (lowJet H x))
    (e : Expression) (t : ℝ) {x : Base} (hx : x ∈ U) :
    (e.coordinatePullback T S K).eval H (x,t) = e.eval G (T x,t) := by
  induction e with
  | coeff c =>
    change c (K (lowJet H x),t) = c (lowJet G (T x),t)
    rw [hjet x hx]
  | atom w a e ih =>
    rw [coordinatePullback,eval_mul,jetPullback_eval hT hS hU hinv hG hH hrel w a t x hx,ih]
    rfl
  | add e f ihe ihf =>
    change (e.coordinatePullback T S K).eval H (x,t)+
      (f.coordinatePullback T S K).eval H (x,t) = _
    rw [ihe,ihf]
    rfl

end Expression

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CoordinatePolynomialPullback
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

lemma inverse_differential_of_local_inverse {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (x : Base)
    (hST : S (T x) = x) (hTS : (T ∘ S) =ᶠ[𝓝 (T x)] id) :
    (fderiv ℝ T x).comp (fderiv ℝ S (T x)) = ContinuousLinearMap.id ℝ Base := by
  have hd := hTS.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp (T x) (hT.differentiable (by simp) _) (hS.differentiable (by simp) _),
    hST,fderiv_id] at hd
  exact hd

namespace Expression

lemma localCoordinatePullback_eval {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (e : Expression) (t : ℝ) {x : Base} (hx : x ∈ U) :
    (e.localCoordinatePullback T S).eval H (x,t) = e.eval G (T x,t) := by
  apply coordinatePullback_eval hT hS hU
    (fun y hy => inverse_differential_of_local_inverse hT hS y (hST y hy) (hTS y hy))
    hG hH hrel _ e t hx
  intro y hy
  have hgerm : H =ᶠ[𝓝 y] (G ∘ T) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact hrel z hz
  exact (lowJetCoordinateChange_local_inverse hH hS y (hST y hy) (hTS y hy) hgerm).symm

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
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

@[simp] lemma eval_scale (a : ℝ) (e : Expression) (G : Base → Space) (z : Base × ℝ) :
    (e.scale a).eval G z = a * e.eval G z := eval_mapCoeff_mul e G (fun _ => a) z

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CoordinateTensorPullback
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

lemma tensorCoordinateJacobian_sum (T : Base → Base) (x : Base)
    (A : PhaseMean.Tensor) (k : Fin 3) :
    (∑ l : Fin 3, tensorCoordinateJacobian T k l x * A l) =
      tensorCoordinatePullbackValue T x A k := by
  rw [Fin.sum_univ_three]
  let u := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.firstDirection k))
  let v := fderiv ℝ T x (planeCoordinateIsometry.symm (PhaseMean.secondDirection k))
  change u 0 * v 0 * A 0 + (u 0 * v 1 + u 1 * v 0) * A 1 + u 1 * v 1 * A 2 =
    A 0 * u 0 * v 0 + A 1 * (u 0 * v 1 + u 1 * v 0) + A 2 * u 1 * v 1
  ring

namespace TensorExpression

/-- An exact tensor evaluation identity from genuine local inverse germs
and the actual map relation. -/
theorem coordinatePullback_eval {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (E : TensorExpression) (t : ℝ) {x : Base} (hx : x ∈ U) :
    eval (coordinatePullback E T S) H (x,t) =
      tensorCoordinatePullbackValue T x (eval E G (T x,t)) := by
  funext k
  change (Expression.sumFinset Finset.univ (fun l : Fin 3 =>
    (Expression.coeff (tensorJacobianCoefficient T k l)).mul ((E l).localCoordinatePullback T S))).eval
      H (x,t) = _
  rw [Expression.sumFinset,Expression.eval_sumList,
    ← List.sum_toFinset _ Finset.univ.nodup_toList,Finset.toList_toFinset]
  simp only [Expression.eval_mul,Expression.eval,tensorJacobianCoefficient,lowPosition_lowJet]
  simp_rw [Expression.localCoordinatePullback_eval hT hS hU hST hTS hG hH hrel _ t hx]
  exact tensorCoordinateJacobian_sum T x (eval E G (T x,t)) k

end TensorExpression

namespace Perturbation

lemma coordinatePolynomialValue_eq_tensor_sum {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space) (t : ℝ) (x : Base) :
    coordinatePolynomialValue P ε G t (planeCoordinateIsometry x) =
      ∑ r : Fin n, ε ^ (r.val+1) • TensorExpression.eval (fun k => P k r) G (x,t) := by
  funext k
  simp only [coordinatePolynomialValue,LinearIsometryEquiv.symm_apply_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,TensorExpression.eval]

/-- The three-component finite polynomial transforms covariantly under
smooth coordinate changes. -/
theorem tensorPolynomialCoordinatePullback_eval {n : ℕ}
    (P : Fin 3 → Fin n → Expression) {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x))
    (ε t : ℝ) {x : Base} (hx : x ∈ U) :
    coordinatePolynomialValue (tensorPolynomialCoordinatePullback P T S) ε H t
        (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x
        (coordinatePolynomialValue P ε G t (planeCoordinateIsometry (T x))) := by
  rw [coordinatePolynomialValue_eq_tensor_sum,coordinatePolynomialValue_eq_tensor_sum,map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul]
  congr 1
  exact TensorExpression.coordinatePullback_eval hT hS hU hST hTS hG hH hrel
    (fun k => P k r) t hx

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_JetMetricCoordinatePullback
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete metric-plus-polynomial operator transforms through fixed
nonlinear coordinates, including its finite periodic error. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open RealModes

lemma metric_coordinate_pullback {F : Base → Space} {T : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hT : ContDiff ℝ ∞ T) (x : Base) :
    realMetricTensor ((F ∘ T) ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x
        (realMetricTensor (F ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry (T x))) := by
  let τ : SmallModes.Base → SmallModes.Base :=
    planeCoordinateIsometry ∘ T ∘ planeCoordinateIsometry.symm
  have hτ : ContDiff ℝ ∞ τ := planeCoordinateIsometry.contDiff.comp
    (hT.comp planeCoordinateIsometry.symm.contDiff)
  have he : (F ∘ planeCoordinateIsometry.symm) ∘ τ =
      (F ∘ T) ∘ planeCoordinateIsometry.symm := by
    funext p
    simp [τ]
  rw [← he,realMetricTensor_comp
    ((hF.comp planeCoordinateIsometry.symm.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) (hτ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _)]
  have hd : fderiv ℝ τ (planeCoordinateIsometry x) = tensorCoordinateDerivative T x := by
    dsimp [τ]
    rw [fderiv_comp _ (planeCoordinateIsometry.differentiableAt)
      ((hT.comp planeCoordinateIsometry.symm.contDiff).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _),
      fderiv_comp _ (hT.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) _) planeCoordinateIsometry.symm.differentiableAt]
    simp only [LinearIsometryEquiv.fderiv,LinearIsometryEquiv.symm_apply_apply]
    rfl
  simp only [PhaseMean.pullbackField,hd,τ,Function.comp_apply,LinearIsometryEquiv.symm_apply_apply,tensorCoordinatePullbackValue]

lemma metric_coordinate_pullback_germ {F H : Base → Space} {T : Base → Base}
    (hF : ContDiff ℝ ∞ F) (hT : ContDiff ℝ ∞ T) {x : Base}
    (hrel : H =ᶠ[𝓝 x] F ∘ T) :
    realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x
        (realMetricTensor (F ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry (T x))) := by
  have hh : H ∘ planeCoordinateIsometry.symm =ᶠ[𝓝 (planeCoordinateIsometry x)]
      (F ∘ T) ∘ planeCoordinateIsometry.symm :=
    hrel.comp_tendsto (by simpa only [LinearIsometryEquiv.symm_apply_apply] using
      (planeCoordinateIsometry.symm.continuous.tendsto (planeCoordinateIsometry x)))
  rw [← metric_coordinate_pullback hF hT]
  ext i
  simp only [realMetricTensor_apply,realMetric,SmallModes.coordDeriv,hh.fderiv_eq]

namespace Perturbation
lemma coordinateMetricMap_coordinatePullback {n : ℕ} (P : Fin 3 → Fin n → Expression)
    {T S : Base → Base} (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, T ∘ S =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hrel : ∀ x ∈ U, H x = G (T x)) (z : ℝ) {x : Base} (hx : x ∈ U) :
    coordinateMetricMap (tensorPolynomialCoordinatePullback P T S) z H (planeCoordinateIsometry x) =
      tensorCoordinatePullbackValue T x (coordinateMetricMap P z G (planeCoordinateIsometry (T x))) := by
  have hh : H =ᶠ[𝓝 x] G ∘ T := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hrel y hy
  simp only [coordinateMetricMap,Pi.add_apply,map_add]
  rw [metric_coordinate_pullback_germ hG hT hh,
    tensorPolynomialCoordinatePullback_eval P hT hS hU hST hTS hG hH hrel z 0 hx]

lemma coordinate_remainder_pullback {n : ℕ} (P : Fin 3 → Fin n → Expression)
    {T S : Base → Base} (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, T ∘ S =ᶠ[𝓝 (T x)] id)
    {G H V W : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hV : ContDiff ℝ ∞ V)
    (hbase : ∀ x ∈ U, H x = G (T x)) (hvalue : ∀ x ∈ U, W x = V (T x))
    (B : Base → PhaseMean.Tensor) (z : ℝ) {x : Base} (hx : x ∈ U) :
    realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        coordinateMetricMap (tensorPolynomialCoordinatePullback P T S) z H (planeCoordinateIsometry x) -
        tensorCoordinatePullbackValue T x (B (T x)) =
      tensorCoordinatePullbackValue T x
        (realMetricTensor (V ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry (T x)) -
          coordinateMetricMap P z G (planeCoordinateIsometry (T x)) - B (T x)) := by
  have hv : W =ᶠ[𝓝 x] V ∘ T := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hvalue y hy
  rw [metric_coordinate_pullback_germ hV hT hv,
    coordinateMetricMap_coordinatePullback P hT hS hU hST hTS hG hH hbase z hx,map_sub,map_sub]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

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

lemma supportedChartPullback_smooth (e : OpenPartialHomeomorph Base Base)
    {χ : Base → ℝ} {f : Base → V} (he : ContDiff ℝ ∞ e)
    (hχ : ContDiff ℝ ∞ χ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (supportedChartPullback e χ f) := hχ.smul (hf.comp he)

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasAnsatz
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
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

lemma cutoffTensorPolynomial_eval {n : ℕ} (χ : Base → ℝ)
    (P : Fin 3 → Fin n → Expression) (G : Base → Space) (z t : ℝ) (x : Base) :
    coordinatePolynomialValue (cutoffTensorPolynomial χ P) z G t (planeCoordinateIsometry x) =
      χ x • coordinatePolynomialValue P z G t (planeCoordinateIsometry x) := by
  ext k
  simp only [coordinatePolynomialValue,cutoffTensorPolynomial,Expression.eval_mul,
    Expression.eval,lowPosition_lowJet,LinearIsometryEquiv.symm_apply_apply,Pi.smul_apply,smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalizedMetricDefect
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact localized metric defect in a nonlinear chart. The cutoff is
one on the actual map increment, so no boundary metric term is discarded. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open RealModes

lemma coordinateMetric_eq_of_sub_notMem_tsupport {H W : Base → Space} {x : Base}
    (hx : x ∉ tsupport (W-H)) :
    realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) =
      realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) := by
  have he : W =ᶠ[𝓝 x] H := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    exact sub_eq_zero.mp hy
  have hh : W ∘ planeCoordinateIsometry.symm =ᶠ[𝓝 (planeCoordinateIsometry x)]
      H ∘ planeCoordinateIsometry.symm :=
    he.comp_tendsto (by simpa only [LinearIsometryEquiv.symm_apply_apply] using
      (planeCoordinateIsometry.symm.continuous.tendsto (planeCoordinateIsometry x)))
  ext k
  simp only [realMetricTensor_apply,realMetric,SmallModes.coordDeriv,hh.fderiv_eq]

namespace Perturbation

theorem localized_metric_defect {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) {χ : Base → ℝ}
    (hχ : tsupport χ ⊆ e.source)
    {G H V W : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    (hV : ContDiff ℝ ∞ V)
    (hbase : ∀ x ∈ e.source, H x = G (e x))
    (hvalue : ∀ x ∈ e.source, W x = V (e x))
    (hone : ∀ x ∈ tsupport (W-H), χ x = 1)
    (B : Base → PhaseMean.Tensor) (z : ℝ) (x : Base) :
    realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        coordinatePolynomialValue
          (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))
          z H 0 (planeCoordinateIsometry x) - localizedTensorPullback e χ B x =
      localizedTensorPullback e χ
        (fun y => realMetricTensor (V ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry y) -
          coordinateMetricMap P z G (planeCoordinateIsometry y) - B y) x := by
  rw [cutoffTensorPolynomial_eval]
  have hfix : χ x •
      (realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
       realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x)) =
      realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
       realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) := by
    by_cases hx : x ∈ tsupport (W-H)
    · rw [hone x hx,one_smul]
    · rw [coordinateMetric_eq_of_sub_notMem_tsupport hx,sub_self,smul_zero]
  by_cases hzero : χ x = 0
  · rw [hzero,zero_smul] at hfix
    simp only [localizedTensorPullback,hzero,zero_smul,sub_zero]
    exact hfix.symm
  have hx : x ∈ e.source := hχ (subset_tsupport χ hzero)
  have hTS : ∀ y ∈ e.source, e ∘ e.symm =ᶠ[𝓝 (e y)] id := by
    intro y hy
    filter_upwards [e.open_target.mem_nhds (e.map_source hy)] with q hq
    exact e.right_inv hq
  have hr := coordinate_remainder_pullback P he hi e.open_source
    (fun _ hx => e.left_inv hx) hTS hG hH hV hbase hvalue B z hx
  have hp := congrArg (fun a : PhaseMean.Tensor => χ x • a) hr
  simp only [coordinateMetricMap,Pi.add_apply,smul_sub,smul_add] at hp
  dsimp only [localizedTensorPullback]
  rw [← hfix]
  simpa only [smul_sub,sub_add_eq_sub_sub,coordinateMetricMap,Pi.add_apply] using hp

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_SupportedPhaseMetric
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.exactCellCutoff_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supportedPlaneWeight_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport_jetSupport _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.onModeSupport_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.tensorChartPush_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_source _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_symm_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart_target _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_apply _root_.OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv_symm_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_pieceSupport _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.coe_supportCompact _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.splitSupported_apply _root_.OAI.ClosedSurfaceR4.PhasePartitions.CompactPhasePartition.supportedWeight_apply _root_.OAI.ClosedSurfaceR4.RealModes.secondTensorFromJet_realTwoJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual supported phase-chart map realizes the localized metric
identity. Its cutoff is fixed before the fast scale is chosen. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation

theorem supported_phase_metric_defect {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) {χ : Base → ℝ}
    (hχ : tsupport χ ⊆ e.source) {K : Set Base} (hK : IsCompact K)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    {H V : Base → JetPolynomial.Space} (hH : ContDiff ℝ ∞ H) (hV : ContDiff ℝ ∞ V)
    (hs : tsupport (V-H ∘ e.symm) ⊆ K)
    (B : Base → PhaseMean.Tensor) (z : ℝ) (x : Base) :
    let W := H + supportedChartPullback e χ (V-H ∘ e.symm)
    RealModes.realMetricTensor (W ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        RealModes.realMetricTensor (H ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry x) -
        coordinatePolynomialValue
          (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))
          z H 0 (planeCoordinateIsometry x) - localizedTensorPullback e χ B x =
      localizedTensorPullback e χ
        (fun y => RealModes.realMetricTensor (V ∘ planeCoordinateIsometry.symm) (planeCoordinateIsometry y) -
          coordinateMetricMap P z (H ∘ e.symm) (planeCoordinateIsometry y) - B y) x := by
  let f := supportedChartPullback e χ (V-H ∘ e.symm)
  have hsf : tsupport f ⊆ e.symm '' K := supportedChartPullback_support e hi hK hχ hs
  have hsub : (H+f)-H = f := by funext y; simp
  apply localized_metric_defect P e he hi hχ (hH.comp hi) hH hV
  · intro y hy
    simp only [Function.comp_apply,e.left_inv hy]
  · intro y hy
    have hh := supportedChartPullback_eq e hs hone hy
    change H y + supportedChartPullback e χ (V-H ∘ e.symm) y = V (e y)
    rw [hh]
    simp only [Pi.sub_apply,Function.comp_apply,e.left_inv hy]
    abel
  · intro y hy
    rw [hsub] at hy
    exact hone y (hsf hy)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_NonlinearAtlasMetric
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
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricFiberSpace
local instance nonlinearMetricDualSmul_r9fadc1_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.nonlinearMetricFiberNormed
local instance nonlinearMetricSectionNormed_r9fadc1_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance nonlinearMetricSectionSpace_r9fadc1_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma phaseAtlasAnsatz_defect_oai (i : A.centers) {F : M → Space}
    (hF : ContMDiff planeModel spaceModel ∞ F)
    (e : OpenPartialHomeomorph JetPolynomial.Base JetPolynomial.Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm)
    {χ : JetPolynomial.Base → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχs : tsupport χ ⊆ e.source)
    {O : TopologicalSpace.Opens JetPolynomial.Base} (U : ℕ → Family O Space)
    {K : Set JetPolynomial.Base} (hK : IsCompact K) (hKO : K ⊆ O)
    (hKA : e.symm '' K ⊆ (A.chartWeightCompact i : Set JetPolynomial.Base))
    (hzero : ∀ j x, x ∉ K → (U j).val x = 0)
    (hone : ∀ x ∈ e.symm '' K, χ x = 1)
    (ℓ : JetPolynomial.Base →L[ℝ] ℝ) (L : ℕ) (z : ℝ)
    {n : ℕ} (P : Fin 3 → Fin n → Expression)
    (γ : ∀ x : M, CovariantTwoTensor x) (B : JetPolynomial.Base → PhaseMean.Tensor) :
    inducedTensor (A.phaseAtlasAnsatz i F e χ U ℓ L z) -
        (γ + A.bundleRestore A.tensorTriv i (fun y => fiberFromThree (localizedTensorPullback e χ B y))) =
      (A.atlasPolynomialMetric (A.primitiveAtlasPolynomial i
        (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm))) z F - γ) +
      A.bundleRestore A.tensorTriv i (fun y => fiberFromThree
        (localizedTensorPullback e χ (A.phaseAtlasRemainder i F e U ℓ L z P B) y)) := by
  let f := A.phaseAtlasLocalIncrement i F e χ U ℓ L z
  have hf := A.phaseAtlasLocalIncrement_smooth i hF e he hi hχ U hK.isClosed hKO hzero ℓ L z
  have hs := (A.phaseAtlasLocalIncrement_support i F e hi hχs U hK hzero ℓ L z).trans hKA
  have hd := A.supported_local_metric_defect i hF f hf hs
    (cutoffTensorPolynomial χ (tensorPolynomialCoordinatePullback P e e.symm)) z γ
    (fun y => localizedTensorPullback e χ B (planeCoordinateIsometry.symm y))
  simp only [LinearIsometryEquiv.symm_apply_apply] at hd
  change inducedTensor (F+restore (i : M) (A.outer i) f) - _ = _
  rw [hd]
  congr 1
  congr 1
  funext y
  apply congrArg fiberFromThree
  let V := spaceCoordinates ∘ finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z
  let H := A.jetChartMap i F
  have hH : ContDiff ℝ ∞ H := A.jetChartMap_smooth i hF
  have hV : ContDiff ℝ ∞ V := spaceCoordinates.contDiff.comp
    (finiteAnsatz_smooth_global ((A.vectorChartRead_smooth i hF).comp hi) U hK.isClosed hKO
      (fun j x _ hx => hzero j x hx) ℓ L z)
  have hsupport : tsupport (V-H ∘ e.symm) ⊆ K := by
    have hz := finiteAnsatz_tsupport_sub (A.vectorChartRead i F ∘ e.symm) U hK.isClosed hzero ℓ L z
    have hmaps : V-H ∘ e.symm = spaceCoordinates ∘
        (finiteAnsatz (A.vectorChartRead i F ∘ e.symm) U ℓ L z - A.vectorChartRead i F ∘ e.symm) := by
      funext x
      exact (map_sub spaceCoordinates _ _).symm
    rw [hmaps]
    exact (tsupport_comp_subset (map_zero spaceCoordinates) _).trans hz
  have hv := supported_phase_metric_defect P e he hi hχs hK hone hH hV hsupport B z y
  have hW : H + supportedChartPullback e χ (V-H ∘ e.symm) =
      spaceCoordinates ∘ (A.vectorChartRead i F + f) := by
    funext x
    simp only [Pi.add_apply,Pi.sub_apply,Function.comp_apply,supportedChartPullback,
      V,H,jetChartMap,f,phaseAtlasLocalIncrement,map_add,map_sub,map_smul]
  rw [hW] at hv
  dsimp only [V,H] at hv
  dsimp only [localizedTensorPullback,phaseAtlasRemainder] at hv ⊢
  simpa only [coordinateMetricMap,Pi.add_apply,sub_add_eq_sub_sub,
    Function.comp_assoc] using hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.phaseAtlasAnsatz_defect_oai.{u_1}
