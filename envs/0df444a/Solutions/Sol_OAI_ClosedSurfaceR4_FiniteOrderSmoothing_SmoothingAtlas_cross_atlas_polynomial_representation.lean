-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:03:32.777164+00:00
-- url     : https://prove2.me/submissions/10224f7a-ec88-4b2e-b470-234be3245ad3

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI011

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_AtlasJetCoordinateRelation
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual localized atlas maps on a coordinate overlap.  The transition
scalar is the square of the outer cutoff.  A nonzero partition weight gives
the needed equality of germs without any extra plateau hypothesis. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma outer_eventually_one_of_weight_ne_zero (i : A.centers) {p : M}
    (hp : A.weight i p ≠ 0) :
    A.outer i =ᶠ[𝓝 p] (fun _ => 1) := by
  have hn : ∀ᶠ q in 𝓝 p, A.weight i q ≠ 0 :=
    (isOpen_ne.preimage (A.weight_smooth i).continuous).mem_nhds hp
  filter_upwards [hn] with q hq
  exact A.outer_one i q (subset_tsupport (A.weight i) hq)

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

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

lemma coordinateLowJetSubstitution_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) :
    ContDiff ℝ ∞ (coordinateLowJetSubstitution T S) :=
  (lowJetCoordinateChange_smooth hS).comp
    ((hT.comp lowPosition.contDiff).prodMk contDiff_id)

lemma inverse_differential_of_local_inverse {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (x : Base)
    (hST : S (T x) = x) (hTS : (T ∘ S) =ᶠ[𝓝 (T x)] id) :
    (fderiv ℝ T x).comp (fderiv ℝ S (T x)) = ContinuousLinearMap.id ℝ Base := by
  have hd := hTS.fderiv_eq (𝕜 := ℝ)
  rw [fderiv_comp (T x) (hT.differentiable (by simp) _) (hS.differentiable (by simp) _),
    hST,fderiv_id] at hd
  exact hd

namespace Expression

lemma localCoordinatePullback_smooth {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.localCoordinatePullback T S).SmoothCoeffs univ :=
  coordinatePullback_smooth hT hS (coordinateLowJetSubstitution_smooth hT hS) he

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

/-- At a boundary of a support it is enough to know the actual map relation
as a germ at the point under consideration. -/
lemma localCoordinatePullback_eval_germ {T S : Base → Base}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {x : Base} (hx : x ∈ U) (hrel : H =ᶠ[𝓝 x] (G ∘ T))
    (e : Expression) (t : ℝ) :
    (e.localCoordinatePullback T S).eval H (x,t) = e.eval G (T x,t) := by
  have hn : {y | H y = G (T y)} ∩ U ∈ 𝓝 x :=
    Filter.inter_mem hrel (hU.mem_nhds hx)
  obtain ⟨V,hVsub,hV,hxV⟩ := mem_nhds_iff.mp hn
  exact localCoordinatePullback_eval hT hS hV
    (fun y hy => hST y (hVsub hy).2) (fun y hy => hTS y (hVsub hy).2)
    hG hH (fun y hy => (hVsub hy).1) e t hxV

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialScalar
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

namespace Perturbation

lemma coordinatePolynomialValue_eq_tensor_sum {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (ε : ℝ) (G : Base → Space) (t : ℝ) (x : Base) :
    coordinatePolynomialValue P ε G t (planeCoordinateIsometry x) =
      ∑ r : Fin n, ε ^ (r.val+1) • TensorExpression.eval (fun k => P k r) G (x,t) := by
  funext k
  simp only [coordinatePolynomialValue,LinearIsometryEquiv.symm_apply_apply,
    Finset.sum_apply,Pi.smul_apply,smul_eq_mul,TensorExpression.eval]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CompactCoordinatePullback
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth representatives of the coordinate transitions on each
compact overlap, with exact local inverses and polynomial tensor transport. -/
noncomputable section
open Set
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial

/-- Both coordinate maps can be extended off a compact overlap. Their
actual inverse identities continue to hold as germs on a smaller open set. -/
theorem compact_coordinate_representatives
    (e : OpenPartialHomeomorph Base Base)
    (he : ContDiffOn ℝ ∞ e e.source) (hi : ContDiffOn ℝ ∞ e.symm e.target)
    {K : Set Base} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧ U ⊆ e.source ∧
      ∃ T S : Base → Base, ContDiff ℝ ∞ T ∧ ContDiff ℝ ∞ S ∧ EqOn T e U ∧
        (∀ x ∈ U, S (T x) = x) ∧
        (∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id) := by
  obtain ⟨W,hW,hKW,hWe,T,hT,hTe⟩ :=
    CollarVelocity.compact_smooth_extension hK e.open_source hKe he
  have himage : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKe)
  obtain ⟨V,hV,hKV,hVe,S,hS,hSe⟩ :=
    CollarVelocity.compact_smooth_extension himage e.open_target
      (by rintro y ⟨x,hx,rfl⟩; exact e.map_source (hKe hx)) hi
  let U := W ∩ T ⁻¹' V
  have hU : IsOpen U := hW.inter (hV.preimage hT.continuous)
  have hUK : K ⊆ U := by
    intro x hx
    refine ⟨hKW hx,?_⟩
    change T x ∈ V
    rw [hTe (hKW hx)]
    exact hKV (mem_image_of_mem e hx)
  have hST : ∀ x ∈ U, S (T x) = x := by
    intro x hx
    rw [hSe hx.2,hTe hx.1,e.left_inv (hWe hx.1)]
  refine ⟨U,hU,hUK,fun _ hx => hWe hx.1,T,S,hT,hS,
    fun _ hx => hTe hx.1,hST,?_⟩
  intro x hx
  have hn : T x ∈ S ⁻¹' W := by
    change S (T x) ∈ W
    rw [hST x hx]
    exact hx.1
  filter_upwards [hV.mem_nhds hx.2,(hW.preimage hS.continuous).mem_nhds hn] with y hy hsy
  change T (S y) = y
  rw [hTe hsy,hSe hy,e.right_inv (hVe hy)]

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasJetRelation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Localized jets can be transported between independently chosen atlases. -/
noncomputable section
open Set Filter Manifold
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

lemma cross_transitionScalar_smoothOn (i : A.centers) (j : B.centers) :
    ContDiffOn ℝ ∞ (A.cross_transitionScalar B i j) (chart (i : M)).target := by
  exact ((B.outer_smooth j).comp_contMDiffOn
    (chart_symm_smooth (i : M))).contDiffOn.pow 2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma cross_vectorChartRead_transition (i : A.centers) (j : B.centers) (G : M → V)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    B.vectorChartRead j G (transition (i : M) (j : M) x) =
      A.cross_transitionScalar B i j x • A.vectorChartRead i G x := by
  have hi : x ∈ (chart (i : M)).target := hx.1
  have hj : transition (i : M) (j : M) x ∈ (chart (j : M)).target :=
    (chart (j : M)).map_source hx.2
  have he : (chart (j : M)).symm (transition (i : M) (j : M) x) =
      (chart (i : M)).symm x :=
    (chart (j : M)).left_inv hx.2
  simp only [vectorChartRead, localize, indicator_of_mem hi, indicator_of_mem hj,
    he, ho, one_pow, one_smul, cross_transitionScalar]

lemma cross_vectorChartRead_transition_eventually (i : A.centers) (j : B.centers) (G : M → V)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    (fun y => B.vectorChartRead j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
      (fun y => A.cross_transitionScalar B i j y • A.vectorChartRead i G y) := by
  have ho := (A.outer_eventually_one_of_weight_ne_zero i hw).comp_tendsto
    ((chart (i : M)).continuousAt_symm hx.1)
  filter_upwards [(transition (i : M) (j : M)).open_source.mem_nhds hx,ho]
    with y hy hoy
  exact A.cross_vectorChartRead_transition B i j G hy hoy

lemma cross_jetChartMap_transition (i : A.centers) (j : B.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    B.jetChartMap j G (transition (i : M) (j : M) x) =
      A.cross_transitionScalar B i j x • A.jetChartMap i G x := by
  change spaceCoordinates (B.vectorChartRead j G (transition (i : M) (j : M) x)) = _
  rw [A.cross_vectorChartRead_transition B i j G hx ho]
  exact map_smul spaceCoordinates _ _

lemma cross_jetChartMap_transition_eventually (i : A.centers) (j : B.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (hw : A.weight i ((chart (i : M)).symm x) ≠ 0) :
    (fun y => B.jetChartMap j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
      (fun y => A.cross_transitionScalar B i j y • A.jetChartMap i G y) := by
  filter_upwards [A.cross_vectorChartRead_transition_eventually B i j G hx hw] with y hy
  change spaceCoordinates (B.vectorChartRead j G (transition (i : M) (j : M) y)) = _
  rw [hy]
  exact map_smul spaceCoordinates _ _

/-- The partition weight removes the boundary case where a germ equal to
one is unavailable. This identity holds on the whole transition domain. -/
lemma cross_weighted_jetChartMap_transition (i : A.centers) (j : B.centers) (G : M → Space)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source) :
    (A.weight i ((chart (i : M)).symm x)) ^ 2 •
        B.jetChartMap j G (transition (i : M) (j : M) x) =
      (A.weight i ((chart (i : M)).symm x)) ^ 2 •
        (A.cross_transitionScalar B i j x • A.jetChartMap i G x) := by
  by_cases hw : A.weight i ((chart (i : M)).symm x) = 0
  · simp only [hw,zero_pow (by decide : 2 ≠ 0),zero_smul]
  · rw [A.cross_jetChartMap_transition B i j G hx
      (A.outer_one i _ (subset_tsupport (A.weight i) hw))]

/-- A fixed compact overlap has a globally smooth transition scalar. It
is chosen before the map, and retains both the weighted identity everywhere
and the unweighted identity of germs on the nonzero weight locus. -/
theorem cross_compact_jetChartMap_transition (i : A.centers) (j : B.centers) {K : Set Base}
    (hK : IsCompact K) (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ a : Base → ℝ, ContDiff ℝ ∞ a ∧ EqOn a (A.cross_transitionScalar B i j) U ∧
        (∀ (G : M → Space) (x : Base), x ∈ U →
          (A.weight i ((chart (i : M)).symm x)) ^ 2 •
              B.jetChartMap j G (transition (i : M) (j : M) x) =
            (A.weight i ((chart (i : M)).symm x)) ^ 2 • (a x • A.jetChartMap i G x)) ∧
        (∀ (G : M → Space) (x : Base), x ∈ U →
          A.weight i ((chart (i : M)).symm x) ≠ 0 →
            (fun y => B.jetChartMap j G (transition (i : M) (j : M) y)) =ᶠ[𝓝 x]
              (fun y => a y • A.jetChartMap i G y)) := by
  obtain ⟨U,hU,hKU,hUe,a,ha,he⟩ := CollarVelocity.compact_smooth_extension hK
    (transition (i : M) (j : M)).open_source hKe
    ((A.cross_transitionScalar_smoothOn B i j).mono (fun _ hx => hx.1))
  refine ⟨U,hU,hKU,hUe,a,ha,he,?_,?_⟩
  · intro G x hx
    rw [he hx]
    exact A.cross_weighted_jetChartMap_transition B i j G (hUe hx)
  · intro G x hx hw
    filter_upwards [A.cross_jetChartMap_transition_eventually B i j G (hUe hx) hw,
      hU.mem_nhds hx] with y hy hyU
    rw [he hyU]
    exact hy

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_CrossAtlasTensorTransition
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual tensor transitions between independent smoothing atlases. -/
noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Manifold Topology

namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)
open PhaseMean

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberSpace
local instance crossTransitionDualSmul_ra01b31_1 : ∀ p : M,
    ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossTransitionFiberNormed
local instance crossTransitionSectionNormed_ra01b31_1 (p : M) :
    NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossTransitionSectionSpace_ra01b31_1 (p : M) :
    NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
lemma cross_tensorRestoreTransition_smoothOn (i : A.centers) (j : B.centers) :
    ContDiffOn ℝ ∞ (A.cross_tensorRestoreTransition B i j)
      (transition (i : M) (j : M)).source := by
  have hB : ContDiffOn ℝ ∞
      (fun x => ((B.tensorTriv j).coordChangeL ℝ (A.tensorTriv i) ((chart (i : M)).symm x) : TensorFiber →L[ℝ] TensorFiber))
      (transition (i : M) (j : M)).source := by
    apply ContMDiffOn.contDiffOn
    apply (contMDiffOn_coordChangeL (B.tensorTriv j) (A.tensorTriv i)).comp
      ((chart_symm_smooth (i : M)).mono (fun _ hx => hx.1))
    intro x hx
    exact ⟨B.tensorTriv_domain j hx.2,A.tensorTriv_domain i ((chart (i : M)).map_target hx.1)⟩
  have ha : ContDiffOn ℝ ∞ (fun x : Base => B.outer j ((chart (i : M)).symm x))
      (chart (i : M)).target :=
    ((B.outer_smooth j).comp_contMDiffOn (chart_symm_smooth (i : M))).contDiffOn
  have hl : ContDiffOn ℝ ∞ (fun _ : Base => fiberToThree)
      (transition (i : M) (j : M)).source := contDiffOn_const
  have hr : ContDiffOn ℝ ∞ (fun _ : Base => fiberFromThree)
      (transition (i : M) (j : M)).source := contDiffOn_const
  exact (ha.mono (fun _ hx => hx.1)).smul (hl.clm_comp (hB.clm_comp hr))

lemma cross_tensorChartRead_restoreThree (i : A.centers) (j : B.centers) (f : Base → Tensor)
    {x : Base} (hx : x ∈ (transition (i : M) (j : M)).source)
    (ho : A.outer i ((chart (i : M)).symm x) = 1) :
    A.tensorChartRead i (B.bundleRestore B.tensorTriv j (fun y => fiberFromThree (f y))) x =
      A.cross_tensorRestoreTransition B i j x (f (transition (i : M) (j : M) x)) := by
  have hxt : x ∈ (chart (i : M)).target := hx.1
  have hbi := A.tensorTriv_domain i ((chart (i : M)).map_target hx.1)
  have hj : (chart (i : M)).symm x ∈ (chart (j : M)).source := hx.2
  have hbj := B.tensorTriv_domain j hj
  simp only [tensorChartRead,Function.comp_apply,bundleCutoff,bundleComponent,localize,
    indicator_of_mem hxt,bundleRestore,map_smul,ho,one_pow,one_smul]
  rw [(A.tensorTriv i).continuousLinearMapAt_apply_of_mem ℝ hbi,
    (B.tensorTriv j).symmL_apply (R := ℝ) hbj,
    ← (B.tensorTriv j).coordChangeL_apply (R := ℝ) (A.tensorTriv i) ⟨hbj,hbi⟩]
  rfl

lemma cross_tensorChartRead_restore_zero (i : A.centers) (j : B.centers) (f : Base → TensorFiber)
    {x : Base} (hx : x ∈ (chart (i : M)).target)
    (hz : B.outer j ((chart (i : M)).symm x) = 0) :
    A.tensorChartRead i (B.bundleRestore B.tensorTriv j f) x = 0 := by
  simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
    indicator_of_mem hx,bundleComponent,bundleRestore,hz,zero_smul,map_zero,smul_zero]

theorem cross_compact_tensorRestoreTransition (i : A.centers) (j : B.centers) {K : Set Base}
    (hK : IsCompact K) (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ L : Base → Tensor →L[ℝ] Tensor, ContDiff ℝ ∞ L ∧
        EqOn L (A.cross_tensorRestoreTransition B i j) U :=
  CollarVelocity.compact_smooth_extension hK (transition (i : M) (j : M)).open_source hKe
    (A.cross_tensorRestoreTransition_smoothOn B i j)

variable [CompactSpace M]
lemma cross_pairSupport_compact (i : A.centers) (j : B.centers) :
    IsCompact (A.cross_pairSupport B i j) :=
  ((isClosed_tsupport (A.weight i)).inter (isClosed_tsupport (B.outer j))).isCompact.image_of_continuousOn
    ((chart (i : M)).continuousOn.mono (fun _ hx => A.weight_support i hx.1))

omit [CompactSpace M] in
lemma cross_pairSupport_transition (i : A.centers) (j : B.centers) :
    A.cross_pairSupport B i j ⊆ (transition (i : M) (j : M)).source := by
  rintro x ⟨p,⟨hp,hq⟩,rfl⟩
  have hp' := A.weight_support i hp
  refine ⟨(chart (i : M)).map_source hp',?_⟩
  change (chart (i : M)).symm (chart (i : M) p) ∈ (chart (j : M)).source
  rw [(chart (i : M)).left_inv hp']
  exact B.outer_support j hq

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_ScalarJetTransport
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite jet-polynomial transport under multiplication by a fixed
smooth scalar function. This accounts for the atlas outer cutoffs before
coordinate transport. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

lemma coordinatePartial_mul {a f : Base → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (v : Fin 2) (x : Base) :
    coordinatePartial (fun y => a y * f y) v x =
      a x * coordinatePartial f v x + f x * coordinatePartial a v x := by
  change fderiv ℝ (fun y => a y * f y) x (coordinateVector v) = _
  rw [fderiv_fun_mul (ha.differentiable (by simp) x) (hf.differentiable (by simp) x)]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rfl

lemma coordinatePartial_coordinatePartial_mul {a f : Base → ℝ}
    (ha : ContDiff ℝ ∞ a) (hf : ContDiff ℝ ∞ f) (v w : Fin 2) (x : Base) :
    coordinatePartial (coordinatePartial (fun y => a y * f y) w) v x =
      a x * coordinatePartial (coordinatePartial f w) v x +
      coordinatePartial f w x * coordinatePartial a v x +
      coordinatePartial a w x * coordinatePartial f v x +
      f x * coordinatePartial (coordinatePartial a w) v x := by
  have he : coordinatePartial (fun y => a y * f y) w =
      fun y => a y * coordinatePartial f w y + f y * coordinatePartial a w y :=
    funext (coordinatePartial_mul ha hf w)
  change fderiv ℝ (coordinatePartial (fun y => a y * f y) w) x (coordinateVector v) = _
  rw [he,fderiv_fun_add
    ((ha.mul (coordinatePartial_smooth hf w)).differentiable (by simp) x)
    ((hf.mul (coordinatePartial_smooth ha w)).differentiable (by simp) x)]
  simp only [add_apply]
  change coordinatePartial (fun y => a y * coordinatePartial f w y) v x +
      coordinatePartial (fun y => f y * coordinatePartial a w y) v x = _
  rw [coordinatePartial_mul ha (coordinatePartial_smooth hf w),
    coordinatePartial_mul hf (coordinatePartial_smooth ha w)]
  ring

lemma scalarJetFirst_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (v : Fin 2) (k : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => scalarJetFirst a p.1 p.2 v k) := by
  exact ((ha.comp contDiff_fst).mul
    ((ContinuousLinearMap.proj (.inr (firstJetSlot v,k)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd)).add
    (((ContinuousLinearMap.proj (.inr (0,k)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd).mul
      ((coordinatePartial_smooth ha v).comp contDiff_fst))

lemma scalarJetSecond_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (v w : Fin 2) (k : Fin 4) :
    ContDiff ℝ ∞ (fun p : Base × LowJet => scalarJetSecond a p.1 p.2 v w k) := by
  have hp (i : Fin 7) : ContDiff ℝ ∞ (fun p : Base × LowJet => p.2 (.inr (i,k))) :=
    (ContinuousLinearMap.proj (.inr (i,k)) : LowJet →L[ℝ] ℝ).contDiff.comp contDiff_snd
  exact ((((ha.comp contDiff_fst).mul (hp (secondJetSlot v w))).add
    ((hp (firstJetSlot w)).mul ((coordinatePartial_smooth ha v).comp contDiff_fst))).add
    (((coordinatePartial_smooth ha w).comp contDiff_fst).mul (hp (firstJetSlot v)))).add
    ((hp 0).mul ((coordinatePartial_smooth (coordinatePartial_smooth ha w) v).comp contDiff_fst))

lemma lowJetScalarProduct_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (lowJetScalarProduct a) := by
  apply contDiff_pi.mpr
  intro i
  cases i with
  | inl i =>
    exact (ContinuousLinearMap.proj i : Base →L[ℝ] ℝ).contDiff.comp
      (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Base × LowJet → Base))
  | inr i =>
    rcases i with ⟨w,k⟩
    fin_cases w
    · have hp : ContDiff ℝ ∞
          (fun p : Base × LowJet => p.2 (Sum.inr ((0 : Fin 7),k))) :=
        (ContinuousLinearMap.proj (Sum.inr ((0 : Fin 7),k) : LowIndex) : LowJet →L[ℝ] ℝ).contDiff.comp
          (contDiff_snd : ContDiff ℝ ∞ (Prod.snd : Base × LowJet → LowJet))
      exact (ha.comp
        (contDiff_fst : ContDiff ℝ ∞ (Prod.fst : Base × LowJet → Base))).mul hp
    · exact scalarJetFirst_smooth ha 0 k
    · exact scalarJetFirst_smooth ha 1 k
    · exact scalarJetSecond_smooth ha 0 0 k
    · exact scalarJetSecond_smooth ha 0 1 k
    · exact scalarJetSecond_smooth ha 1 0 k
    · exact scalarJetSecond_smooth ha 1 1 k

lemma lowJetScalarProduct_eval {a : Base → ℝ} {G : Base → Space}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) (x : Base) :
    lowJetScalarProduct a (x,lowJet G x) = lowJet (fun y => a y • G y) x := by
  funext i
  cases i with
  | inl i => rfl
  | inr i =>
    rcases i with ⟨w,k⟩
    have hfirst (v : Fin 2) : scalarJetFirst a x (lowJet G x) v k =
        coordinatePartial (fun y => a y * G y k) v x := by
      rw [coordinatePartial_mul ha (contDiff_pi.mp hG k)]
      simp only [scalarJetFirst,lowJet_first_slot]
      rfl
    have hsecond (v w : Fin 2) : scalarJetSecond a x (lowJet G x) v w k =
        coordinatePartial (coordinatePartial (fun y => a y * G y k) w) v x := by
      rw [coordinatePartial_coordinatePartial_mul ha (contDiff_pi.mp hG k)]
      simp only [scalarJetSecond,lowJet_first_slot,lowJet_second_slot]
      rfl
    fin_cases w
    · rfl
    · exact hfirst 0
    · exact hfirst 1
    · exact hsecond 0 0
    · exact hsecond 0 1
    · exact hsecond 1 0
    · exact hsecond 1 1

lemma scalarLowJetSubstitution_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (scalarLowJetSubstitution a) :=
  (lowJetScalarProduct_smooth ha).comp (lowPosition.contDiff.prodMk contDiff_id)

@[simp] lemma scalarLowJetSubstitution_eval {a : Base → ℝ} {G : Base → Space}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) (x : Base) :
    scalarLowJetSubstitution a (lowJet G x) = lowJet (fun y => a y • G y) x := by
  simpa only [scalarLowJetSubstitution,lowPosition_lowJet] using lowJetScalarProduct_eval ha hG x

lemma scalarProductAtom_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    (w : List (Fin 2)) (k : Fin 4) : (scalarProductAtom a w k).SmoothCoeffs univ := by
  induction w with
  | nil => exact (ha.comp (lowPosition.contDiff.comp contDiff_fst)).contDiffOn
  | cons v w ih => exact Expression.smoothCoeffs_slow isOpen_univ v ih

lemma scalarProductAtom_eval {a : Base → ℝ} {G : Base → Space}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G)
    (w : List (Fin 2)) (k : Fin 4) (t : ℝ) (x : Base) :
    (scalarProductAtom a w k).eval G (x,t) = jet (fun y => a y • G y) w k x := by
  induction w generalizing x with
  | nil =>
    change G x k * a (lowPosition (lowJet G x)) = a x * G x k
    rw [lowPosition_lowJet]
    ring
  | cons v w ih =>
    rw [scalarProductAtom,Expression.eval_slow isOpen_univ isOpen_univ hG
      (mapsTo_univ _ _) v (scalarProductAtom_smooth ha w k) (mem_univ x) t]
    have he : (fun y => (scalarProductAtom a w k).eval G (y,t)) =
        jet (fun y => a y • G y) w k := funext ih
    rw [he]
    rfl

namespace Expression

lemma scalarProductPullback_smooth {a : Base → ℝ} (ha : ContDiff ℝ ∞ a)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (scalarProductPullback a e).SmoothCoeffs univ := by
  induction e with
  | coeff c =>
    have hc : ContDiff ℝ ∞ c :=
      contDiffOn_univ.mp (by simpa only [SmoothCoeffs,univ_prod_univ] using he)
    exact (hc.comp (((scalarLowJetSubstitution_smooth ha).comp contDiff_fst).prodMk
      contDiff_snd)).contDiffOn
  | atom w k e ih => exact smoothCoeffs_mul (scalarProductAtom_smooth ha w k) (ih he)
  | add e f ihe ihf => exact ⟨ihe he.1,ihf he.2⟩

lemma scalarProductPullback_eval {a : Base → ℝ} {G : Base → Space}
    (ha : ContDiff ℝ ∞ a) (hG : ContDiff ℝ ∞ G) (e : Expression) (t : ℝ) (x : Base) :
    (scalarProductPullback a e).eval G (x,t) = e.eval (fun y => a y • G y) (x,t) := by
  induction e with
  | coeff c =>
    change c (scalarLowJetSubstitution a (lowJet G x),t) = _
    rw [scalarLowJetSubstitution_eval ha hG]
    rfl
  | atom w k e ih =>
    rw [scalarProductPullback,eval_mul,scalarProductAtom_eval ha hG,ih]
    rfl
  | add e f ihe ihf =>
    change (scalarProductPullback a e).eval G (x,t) +
      (scalarProductPullback a f).eval G (x,t) = _
    rw [ihe,ihf]
    rfl

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Atlas_LocalizedCoordinatePullback
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pullback of a polynomial through a local coordinate change and the
actual scalar localization of its input map. -/
noncomputable section
open Set
open scoped ContDiff Topology BigOperators
namespace ClosedSurfaceR4.JetPolynomial
namespace Expression

lemma localizedCoordinatePullback_smooth {T S : Base → Base} {a : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a)
    {e : Expression} (he : e.SmoothCoeffs univ) :
    (e.localizedCoordinatePullback T S a).SmoothCoeffs univ :=
  scalarProductPullback_smooth ha (localCoordinatePullback_smooth hT hS he)

lemma localizedCoordinatePullback_eval {T S : Base → Base} {a : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {x : Base} (hx : x ∈ U)
    (hrel : (fun y => a y • H y) =ᶠ[𝓝 x] (G ∘ T))
    (e : Expression) (t : ℝ) :
    (e.localizedCoordinatePullback T S a).eval H (x,t) = e.eval G (T x,t) := by
  rw [localizedCoordinatePullback,scalarProductPullback_eval ha hH]
  exact localCoordinatePullback_eval_germ hT hS hU hST hTS hG (ha.smul hH) hx hrel e t

end Expression
namespace Perturbation

lemma localizedPolynomialPullback_smooth {n : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {T S : Base → Base} {a : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a)
    (k : Fin 3) (r : Fin n) :
    (localizedPolynomialPullback P T S a k r).SmoothCoeffs univ :=
  Expression.localizedCoordinatePullback_smooth hT hS ha (hP k r)

lemma localizedPolynomialPullback_eval {n : ℕ} (P : Fin 3 → Fin n → Expression)
    {T S : Base → Base} {a : Base → ℝ}
    (hT : ContDiff ℝ ∞ T) (hS : ContDiff ℝ ∞ S) (ha : ContDiff ℝ ∞ a)
    {U : Set Base} (hU : IsOpen U)
    (hST : ∀ x ∈ U, S (T x) = x)
    (hTS : ∀ x ∈ U, (T ∘ S) =ᶠ[𝓝 (T x)] id)
    {G H : Base → Space} (hG : ContDiff ℝ ∞ G) (hH : ContDiff ℝ ∞ H)
    {x : Base} (hx : x ∈ U)
    (hrel : (fun y => a y • H y) =ᶠ[𝓝 x] (G ∘ T)) (ε t : ℝ) :
    coordinatePolynomialValue (localizedPolynomialPullback P T S a) ε H t
        (planeCoordinateIsometry x) =
      coordinatePolynomialValue P ε G t (planeCoordinateIsometry (T x)) := by
  funext k
  simp only [coordinatePolynomialValue,LinearIsometryEquiv.symm_apply_apply]
  apply Finset.sum_congr rfl
  intro r _
  rw [localizedPolynomialPullback,
    Expression.localizedCoordinatePullback_eval hT hS ha hU hST hTS hG hH hx hrel]

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_TensorExpressionLinearMap
attribute [-instance] _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.realTensorChartPull_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.scalarLowJetSubstitution_eval _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed smooth changes of tensor trivialization act on finite jet
polynomials by finite linear combinations with positional coefficients. -/
noncomputable section
open Set
open scoped ContDiff BigOperators
namespace ClosedSurfaceR4.JetPolynomial

lemma tensorLinearCoefficient_smooth
    {L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor}
    (hL : ContDiff ℝ ∞ L) (k l : Fin 3) :
    ContDiff ℝ ∞ (tensorLinearCoefficient L k l) := by
  have hs : ContDiff ℝ ∞ (fun x => L x (Pi.single l 1) k) :=
    contDiff_pi.mp (hL.clm_apply contDiff_const) k
  exact hs.comp (lowPosition.contDiff.comp contDiff_fst)

namespace TensorExpression

lemma mapLinear_smooth {L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor}
    (hL : ContDiff ℝ ∞ L) {E : TensorExpression}
    (hE : ∀ k, (E k).SmoothCoeffs univ) (k : Fin 3) :
    (mapLinear L E k).SmoothCoeffs univ := by
  apply Expression.smoothCoeffs_sumFinset
  intro l _
  exact Expression.smoothCoeffs_mul (tensorLinearCoefficient_smooth hL k l).contDiffOn (hE l)

lemma mapLinear_eval (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor)
    (E : TensorExpression) (G : Base → Space) (x : Base) (t : ℝ) :
    eval (mapLinear L E) G (x,t) = L x (eval E G (x,t)) := by
  have hb : (∑ l : Fin 3, (eval E G (x,t)) l • Pi.single l (1 : ℝ)) = eval E G (x,t) := by
    ext k
    simp [Pi.single_apply]
  rw [← hb,map_sum]
  funext k
  change (Expression.sumFinset Finset.univ (fun l : Fin 3 =>
    (Expression.coeff (tensorLinearCoefficient L k l)).mul (E l))).eval G (x,t) = _
  rw [Expression.sumFinset,Expression.eval_sumList,
    ← List.sum_toFinset _ Finset.univ.nodup_toList,Finset.toList_toFinset]
  simp only [Expression.eval_mul,Expression.eval,tensorLinearCoefficient,lowPosition_lowJet,
    map_smul,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

end TensorExpression

namespace Perturbation

lemma mapTensorPolynomial_smooth {n : ℕ}
    {L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor} (hL : ContDiff ℝ ∞ L)
    {P : Fin 3 → Fin n → Expression} (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    (k : Fin 3) (r : Fin n) : (mapTensorPolynomial L P k r).SmoothCoeffs univ :=
  TensorExpression.mapLinear_smooth hL (fun l => hP l r) k

lemma mapTensorPolynomial_eval {n : ℕ}
    (L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor) (P : Fin 3 → Fin n → Expression)
    (ε : ℝ) (G : Base → Space) (t : ℝ) (x : Base) :
    coordinatePolynomialValue (mapTensorPolynomial L P) ε G t (planeCoordinateIsometry x) =
      L x (coordinatePolynomialValue P ε G t (planeCoordinateIsometry x)) := by
  rw [coordinatePolynomialValue_eq_tensor_sum,coordinatePolynomialValue_eq_tensor_sum,map_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [map_smul]
  congr 1
  exact TensorExpression.mapLinear_eval L (fun l => P l r) G x t

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialFiniteAssembly
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite polynomial families can be padded to a common degree and added
without changing their values or their smooth-coefficient property. -/
noncomputable section
open Set
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial

namespace Expression

lemma eval_sumFinset {ι : Type*} (s : Finset ι) (e : ι → Expression)
    (G : Base → Space) (z : Base × ℝ) :
    (sumFinset s e).eval G z = ∑ i ∈ s, (e i).eval G z := by
  classical
  rw [sumFinset,eval_sumList,← List.sum_toFinset _ s.nodup_toList,
    Finset.toList_toFinset]

end Expression

namespace Perturbation

private lemma sum_fin_zero_extension {α : Type*} [AddCommMonoid α]
    {n N : ℕ} (hnN : n ≤ N) (f : Fin n → α) :
    (∑ r : Fin N, if h : r.val < n then f ⟨r.val,h⟩ else 0) = ∑ r : Fin n, f r := by
  classical
  let g : ℕ → α := fun r => if h : r < n then f ⟨r,h⟩ else 0
  calc
    (∑ r : Fin N, if h : r.val < n then f ⟨r.val,h⟩ else 0) =
        ∑ r ∈ Finset.range N, g r := Fin.sum_univ_eq_sum_range g N
    _ = ∑ r ∈ Finset.range n, g r := by
      symm
      apply Finset.sum_subset (Finset.range_mono hnN)
      intro r _ hr
      have hn : ¬ r < n := fun h => hr (Finset.mem_range.mpr h)
      simp only [g,dite_eq_right hn]
    _ = ∑ r : Fin n, f r := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro r _
      change (if h : r.val < n then f ⟨r.val,h⟩ else 0) = f r
      rw [dite_eq_left r.isLt]

lemma padTensorPolynomial_smooth {n N : ℕ} {P : Fin 3 → Fin n → Expression}
    (hP : ∀ k r, (P k r).SmoothCoeffs univ) (k : Fin 3) (r : Fin N) :
    (padTensorPolynomial P k r).SmoothCoeffs univ := by
  unfold padTensorPolynomial
  split
  · exact hP _ _
  · exact contDiffOn_const

lemma padTensorPolynomial_value {n N : ℕ} (P : Fin 3 → Fin n → Expression)
    (hnN : n ≤ N) (ε : ℝ) (G : Base → Space) (t : ℝ) :
    coordinatePolynomialValue (padTensorPolynomial (N := N) P) ε G t =
      coordinatePolynomialValue P ε G t := by
  classical
  funext p k
  change (∑ r : Fin N, ε ^ (r.val+1) * (padTensorPolynomial P k r).eval G
      (planeCoordinateIsometry.symm p,t)) =
    ∑ r : Fin n, ε ^ (r.val+1) * (P k r).eval G (planeCoordinateIsometry.symm p,t)
  calc
    _ = ∑ r : Fin N, if h : r.val < n then
        ε ^ (r.val+1) * (P k ⟨r.val,h⟩).eval G (planeCoordinateIsometry.symm p,t)
        else 0 := by
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : r.val < n
      · simp only [padTensorPolynomial,dite_eq_left hr]
      · simp only [padTensorPolynomial,dite_eq_right hr,Expression.eval,mul_zero]
    _ = _ := sum_fin_zero_extension hnN
      (fun r => ε ^ (r.val+1) * (P k r).eval G (planeCoordinateIsometry.symm p,t))

lemma le_polynomialFamilyDegree {ι : Type*} [Fintype ι] (n : ι → ℕ) (i : ι) :
    n i ≤ polynomialFamilyDegree n :=
  Finset.le_sup (f := n) (Finset.mem_univ i)

lemma sumTensorPolynomials_smooth {ι : Type*} [Fintype ι] {n : ι → ℕ}
    {P : (i : ι) → Fin 3 → Fin (n i) → Expression}
    (hP : ∀ i k r, (P i k r).SmoothCoeffs univ) (k : Fin 3)
    (r : Fin (polynomialFamilyDegree n)) :
    (sumTensorPolynomials P k r).SmoothCoeffs univ := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  exact padTensorPolynomial_smooth (hP i) k r

lemma sumTensorPolynomials_value {ι : Type*} [Fintype ι] {n : ι → ℕ}
    (P : (i : ι) → Fin 3 → Fin (n i) → Expression)
    (ε : ℝ) (G : Base → Space) (t : ℝ) :
    coordinatePolynomialValue (sumTensorPolynomials P) ε G t =
      ∑ i, coordinatePolynomialValue (P i) ε G t := by
  classical
  funext p k
  simp only [Finset.sum_apply]
  change (∑ r : Fin (polynomialFamilyDegree n), ε ^ (r.val+1) *
      (Expression.sumFinset Finset.univ (fun i => padTensorPolynomial (P i) k r)).eval G
        (planeCoordinateIsometry.symm p,t)) =
    ∑ i, coordinatePolynomialValue (P i) ε G t p k
  simp_rw [Expression.eval_sumFinset,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  exact congrFun (congrFun (padTensorPolynomial_value (P i)
    (le_polynomialFamilyDegree n i) ε G t) p) k

end Perturbation
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_AtlasPolynomialRepresentation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed coordinate representatives of the same global polynomial
tensor. These are derived from the actual read/restore maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepFiberSpace
local instance polyRepDualSmul_ra01b31_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polyRepFiberNormed
local instance polyRepSectionNormed_ra01b31_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polyRepSectionSpace_ra01b31_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
omit [CompactSpace M] in
lemma tensorChartRead_sum {ι : Type*} [Fintype ι] (i : A.centers)
    (u : ι → ∀ p : M, CovariantTwoTensor p) :
    A.tensorChartRead i (∑ k, u k) = ∑ k, A.tensorChartRead i (u k) := by
  classical
  funext x
  by_cases hx : x ∈ (chart (i : M)).target
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_mem hx,bundleComponent,Finset.sum_apply,map_sum,Finset.smul_sum]
  · simp only [tensorChartRead,Function.comp_apply,bundleCutoff,localize,
      indicator_of_notMem hx,map_zero,Finset.sum_apply,Finset.sum_const_zero]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CrossAtlasPolynomialRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_leftParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_lower _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_rightParameter_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.RegularPathCornerChart.reflect_upper _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.GeometryPreservation.boundaryProfileMap_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial in one localized atlas map has an actual finite jet
expression in another chart, on the nonzero partition-weight locus. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
variable (A B : SmoothingAtlas M)

theorem cross_compact_polynomial_coordinate_read (i : A.centers) (j : B.centers) {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {K : Set Base} (hK : IsCompact K)
    (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ P' : Fin 3 → Fin n → Expression, (∀ k r, (P' k r).SmoothCoeffs univ) ∧
        ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
          ∀ (x : Base), x ∈ U → A.weight i ((chart (i : M)).symm x) ≠ 0 →
            ∀ ε t : ℝ,
              coordinatePolynomialValue P' ε (A.jetChartMap i F) t (JetPolynomial.planeCoordinateIsometry x) =
                coordinatePolynomialValue P ε (B.jetChartMap j F) t
                  (JetPolynomial.planeCoordinateIsometry (transition (i : M) (j : M) x)) := by
  let e := transition (i : M) (j : M)
  have hei : ContDiffOn ℝ ∞ e.symm e.target := by
    have hs : e.symm = transition (j : M) (i : M) := by
      simp [e,transition,OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
    rw [hs]
    exact transition_smooth (j : M) (i : M)
  obtain ⟨U₁,hU₁,hKU₁,hU₁e,T,S,hT,hS,hTe,hST,hTS⟩ :=
    JetPolynomial.compact_coordinate_representatives e (transition_smooth (i : M) (j : M)) hei hK hKe
  obtain ⟨U₂,hU₂,hKU₂,hU₂e,a,ha,hae,_,hrel⟩ := A.cross_compact_jetChartMap_transition B i j hK hKe
  let U := U₁ ∩ U₂
  refine ⟨U,hU₁.inter hU₂,fun x hx => ⟨hKU₁ hx,hKU₂ hx⟩,
    fun x hx => hU₁e hx.1,localizedPolynomialPullback P T S a,
    localizedPolynomialPullback_smooth hP hT hS ha,?_⟩
  intro F hF x hx hw ε t
  have hgerm : (fun y => a y • A.jetChartMap i F y) =ᶠ[𝓝 x]
      (B.jetChartMap j F ∘ T) := by
    filter_upwards [hrel F x hx.2 hw,hU₁.mem_nhds hx.1] with y hy hyU
    change a y • A.jetChartMap i F y = B.jetChartMap j F (T y)
    rw [hTe hyU]
    exact hy.symm
  have hv := localizedPolynomialPullback_eval P hT hS ha hU₁ hST hTS
    (B.jetChartMap_smooth j hF) (A.jetChartMap_smooth i hF) hx.1 hgerm ε t
  simpa only [hTe hx.1] using hv

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CrossAtlasRestoredPolynomialRead
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A restored polynomial tensor has a constructed finite jet expression
in every overlapping correction chart. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredReadDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredReadFiberSpace
local instance crossRestoredReadDualSmul_ra01b31_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredReadFiberNormed
local instance crossRestoredReadSectionNormed_ra01b31_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossRestoredReadSectionSpace_ra01b31_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem cross_compact_restored_polynomial_read (i : A.centers) (j : B.centers) {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k r, (P k r).SmoothCoeffs univ)
    {K : Set Base} (hK : IsCompact K)
    (hKe : K ⊆ (transition (i : M) (j : M)).source) :
    ∃ U : Set Base, IsOpen U ∧ K ⊆ U ∧
      U ⊆ (transition (i : M) (j : M)).source ∧
      ∃ P' : Fin 3 → Fin n → Expression, (∀ k r, (P' k r).SmoothCoeffs univ) ∧
        ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
          ∀ (x : Base), x ∈ U → A.weight i ((chart (i : M)).symm x) ≠ 0 →
            ∀ ε t : ℝ,
              coordinatePolynomialValue P' ε (A.jetChartMap i F) t
                  (JetPolynomial.planeCoordinateIsometry x) =
                A.tensorChartRead i (B.bundleRestore B.tensorTriv j
                  (fun y => fiberFromThree (coordinatePolynomialValue P ε
                    (B.jetChartMap j F) t (JetPolynomial.planeCoordinateIsometry y)))) x := by
  obtain ⟨U₁,hU₁,hKU₁,hU₁e,Q,hQ,hvalue⟩ :=
    A.cross_compact_polynomial_coordinate_read B i j P hP hK hKe
  obtain ⟨U₂,hU₂,hKU₂,hU₂e,L,hL,hLe⟩ :=
    A.cross_compact_tensorRestoreTransition B i j hK hKe
  refine ⟨U₁ ∩ U₂,hU₁.inter hU₂,fun x hx => ⟨hKU₁ hx,hKU₂ hx⟩,
    fun x hx => hU₁e hx.1,mapTensorPolynomial L Q,
    mapTensorPolynomial_smooth hL hQ,?_⟩
  intro F hF x hx hw ε t
  have hq := hvalue F hF x hx.1 hw ε t
  have hr := A.cross_tensorChartRead_restoreThree B i j
    (fun y => coordinatePolynomialValue P ε (B.jetChartMap j F) t
      (JetPolynomial.planeCoordinateIsometry y)) (hU₁e hx.1)
    (A.outer_one i _ (subset_tsupport (A.weight i) hw))
  calc
    _ = L x (coordinatePolynomialValue Q ε (A.jetChartMap i F) t
        (JetPolynomial.planeCoordinateIsometry x)) :=
      mapTensorPolynomial_eval L Q ε (A.jetChartMap i F) t x
    _ = L x (coordinatePolynomialValue P ε (B.jetChartMap j F) t
        (JetPolynomial.planeCoordinateIsometry (transition (i : M) (j : M) x))) :=
      congrArg (L x) hq
    _ = A.cross_tensorRestoreTransition B i j x
        (coordinatePolynomialValue P ε (B.jetChartMap j F) t
          (JetPolynomial.planeCoordinateIsometry (transition (i : M) (j : M) x))) :=
      congrArg (fun C : PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor => C
        (coordinatePolynomialValue P ε (B.jetChartMap j F) t
          (JetPolynomial.planeCoordinateIsometry (transition (i : M) (j : M) x)))) (hLe hx.2)
    _ = _ := hr.symm

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CrossAtlasRestoredPolynomial
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global coefficient extensions for one restored polynomial tensor.
The representation holds on the open nonzero partition-weight locus,
including chart points outside the support of the restored term. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredPolyDualAdd
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredPolyFiberSpace
local instance crossRestoredPolyDualSmul_ra01b31_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossRestoredPolyFiberNormed
local instance crossRestoredPolySectionNormed_ra01b31_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossRestoredPolySectionSpace_ra01b31_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem cross_restored_polynomial_representation (i : A.centers) (j : B.centers) {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k r, (P k r).SmoothCoeffs univ) :
    ∃ P' : Fin 3 → Fin n → Expression, (∀ k r, (P' k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ (x : Base), A.chartWeight i x ≠ 0 → ∀ ε t : ℝ,
          coordinatePolynomialValue P' ε (A.jetChartMap i F) t (JetPolynomial.planeCoordinateIsometry x) =
            A.tensorChartRead i (B.bundleRestore B.tensorTriv j
              (fun y => fiberFromThree (coordinatePolynomialValue P ε
                (B.jetChartMap j F) t (JetPolynomial.planeCoordinateIsometry y)))) x := by
  obtain ⟨U,hU,hKU,hUe,Q,hQ,hread⟩ := A.cross_compact_restored_polynomial_read B i j P hP
    (A.cross_pairSupport_compact B i j) (A.cross_pairSupport_transition B i j)
  obtain ⟨χ,hχ,_,_,hχU,hχone⟩ :=
    CollarVelocity.compact_cutoff (A.cross_pairSupport_compact B i j) hU hKU
  let L : Base → PhaseMean.Tensor →L[ℝ] PhaseMean.Tensor :=
    fun x => χ x • ContinuousLinearMap.id ℝ PhaseMean.Tensor
  have hL : ContDiff ℝ ∞ L := hχ.smul contDiff_const
  refine ⟨mapTensorPolynomial L Q,mapTensorPolynomial_smooth hL hQ,?_⟩
  intro F hF x hx ε t
  have hxt : x ∈ (chart (i : M)).target := by
    by_contra hn
    exact hx (by simp only [chartWeight,indicator_of_notMem hn])
  have hw : A.weight i ((chart (i : M)).symm x) ≠ 0 := by
    simpa only [chartWeight,indicator_of_mem hxt] using hx
  have hvalue := mapTensorPolynomial_eval L Q ε (A.jetChartMap i F) t x
  rw [hvalue]
  change χ x • coordinatePolynomialValue Q ε (A.jetChartMap i F) t
    (JetPolynomial.planeCoordinateIsometry x) = _
  by_cases hz : B.outer j ((chart (i : M)).symm x) = 0
  · have hzero := A.cross_tensorChartRead_restore_zero B i j
      (fun y => fiberFromThree (coordinatePolynomialValue P ε (B.jetChartMap j F) t
        (JetPolynomial.planeCoordinateIsometry y))) hxt hz
    by_cases hxU : x ∈ U
    · rw [hread F hF x hxU hw ε t,hzero,smul_zero]
    · have hχx : χ x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hxU (hχU h))
      rw [hχx,zero_smul,hzero]
  · have hxK : x ∈ A.cross_pairSupport B i j := by
      refine ⟨(chart (i : M)).symm x,⟨subset_tsupport _ hw,subset_tsupport _ hz⟩,?_⟩
      exact (chart (i : M)).right_inv hxt
    rw [hχone x hxK,one_smul,hread F hF x (hKU hxK) hw ε t]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CrossAtlasPolynomialRepresentation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Constructed coordinate representatives of the same global polynomial
tensor. These are derived from the actual read/restore maps. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base Expression)
open JetPolynomial.Perturbation
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossPolyRepFiberSpace
local instance crossPolyRepDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))

namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossPolyRepFiberSpace
local instance crossPolyRepDualSmul_ra01b31_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable (A B : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.crossPolyRepFiberNormed
local instance crossPolyRepSectionNormed_ra01b31_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance crossPolyRepSectionSpace_ra01b31_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
/-- Every correction chart reads the globally restored polynomial as a
single finite polynomial in that chart's actual localized map. -/
theorem cross_atlas_polynomial_representation_oai {n : B.centers → ℕ}
    (P : ∀ j : B.centers, Fin 3 → Fin (n j) → Expression)
    (hP : ∀ j k r, (P j k r).SmoothCoeffs univ) (i : A.centers) :
    ∃ Q : Fin 3 → Fin (polynomialFamilyDegree n) → Expression,
      (∀ k r, (Q k r).SmoothCoeffs univ) ∧
      ∀ (F : M → Space), ContMDiff planeModel spaceModel ∞ F →
        ∀ (x : Base), A.chartWeight i x ≠ 0 → ∀ ε : ℝ,
          coordinatePolynomialValue Q ε (A.jetChartMap i F) 0 (JetPolynomial.planeCoordinateIsometry x) =
            A.tensorChartRead i (B.atlasPolynomialValue P ε F) x := by
  classical
  choose Q hQ hvalue using fun j : B.centers =>
    A.cross_restored_polynomial_representation B i j (P j) (hP j)
  refine ⟨sumTensorPolynomials Q,sumTensorPolynomials_smooth hQ,?_⟩
  intro F hF x hx ε
  have hrestore : B.atlasPolynomialValue P ε F =
      ∑ j : B.centers, B.bundleRestore B.tensorTriv j
        (fun y => fiberFromThree (coordinatePolynomialValue (P j) ε (B.jetChartMap j F) 0
          (JetPolynomial.planeCoordinateIsometry y))) := by
    funext p
    simp only [atlasPolynomialValue,tensorPlaneRestore,Finset.sum_apply]
  rw [sumTensorPolynomials_value,hrestore,A.tensorChartRead_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  exact hvalue j F hF x hx ε 0

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation_oai.{u_1} := @OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.cross_atlas_polynomial_representation_oai.{u_1}
