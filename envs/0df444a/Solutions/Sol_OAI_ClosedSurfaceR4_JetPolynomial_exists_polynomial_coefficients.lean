-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.exists_polynomial_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:50:12.197216+00:00
-- url     : https://prove2.me/submissions/dc84ca30-719f-447e-bc48-1e332d1765cd

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI012

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_CovarianceCorrector
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.averageCLM_apply _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.periodicBilinear_apply _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.weightedAverage_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.ofLocal_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.zero_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.OAI.ClosedSurfaceR4.SmoothPeriodicCalculus.bundleFamily_apply _root_.OAI.ClosedSurfaceR4.SmoothPeriodicCalculus.bundle_apply _root_.OAI.ClosedSurfaceR4.SmoothPeriodicCalculus.primitiveFamily_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The covariance solve in paper 094-01, Section 6, equations
`covariance-equation` and `covariance-solve`. The averaging operator below is
the actual normalized Haar integral on the period circle. The finite linear
solve is proved invertible using constant positive speed and connectedness.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma average_smul_const (f : Period → ℝ) (v : E) :
    average (fun t => f t • v) = average f • v := integral_smul_const f v

lemma average_inner_right {f : Period → E} (hf : Continuous f) (m : E) :
    average (fun t => inner ℝ (f t) m) = inner ℝ (average f) m := by
  calc
    _ = average (fun t => inner ℝ m (f t)) := by
      congr 1
      funext t
      exact real_inner_comm _ _
    _ = inner ℝ m (average f) := by
      simpa only [average, innerSL_apply_apply] using
        (innerSL ℝ m).integral_comp_comm (integrable_of_continuous hf)
    _ = _ := real_inner_comm _ _

lemma average_centered_inner {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) (m : E) :
    average (fun t => inner ℝ (V t - v) m) = 0 := by
  rw [average_inner_right (f := fun t => V t - v) (hV.sub continuous_const),
    average_sub (f := V) (g := fun _ => v) hV continuous_const,
    average_const, hv, sub_self, inner_zero_left]

lemma average_centered_tensor {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) (m : E) :
    average (fun t => inner ℝ (V t - v) m • V t) = covariance V v m := by
  have hi : Continuous (fun t => inner ℝ (V t - v) m) :=
    (hV.sub continuous_const).inner continuous_const
  calc
    _ = average (fun t => inner ℝ (V t - v) m • (V t - v) +
          inner ℝ (V t - v) m • v) := by
      congr 1
      funext t
      rw [← smul_add, sub_add_cancel]
    _ = covariance V v m + average (fun t => inner ℝ (V t - v) m • v) :=
      average_add (hi.smul (hV.sub continuous_const)) (hi.smul continuous_const)
    _ = covariance V v m := by
      rw [average_smul_const, average_centered_inner hV hv, zero_smul, add_zero]

theorem average_weighted_correctedScalar {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) {r : Period → ℝ} (hr : Continuous r)
    (q : ℝ) (m : E)
    (hsolve : m - q⁻¹ • covariance V v m = average (fun t => r t • V t)) :
    average (fun t => correctedScalar V v q r m t • V t) = m := by
  have hi : Continuous (fun t => inner ℝ (V t - v) m) :=
    (hV.sub continuous_const).inner continuous_const
  calc
    _ = average (fun t => r t • V t +
          q⁻¹ • (inner ℝ (V t - v) m • V t)) := by
      congr 1
      funext t
      simp only [correctedScalar, add_smul, div_eq_mul_inv, smul_smul]
      rw [mul_comm]
    _ = average (fun t => r t • V t) +
          q⁻¹ • average (fun t => inner ℝ (V t - v) m • V t) := by
      rw [average_add (f := fun t => r t • V t)
          (g := fun t => q⁻¹ • (inner ℝ (V t - v) m • V t))
          (hr.smul hV) (continuous_const.smul (hi.smul hV)),
        average_const_smul]
    _ = average (fun t => r t • V t) + q⁻¹ • covariance V v m := by
      rw [average_centered_tensor hV hv]
    _ = m := (sub_eq_iff_eq_add.mp hsolve).symm

theorem average_correctedVector {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) {r : Period → ℝ} (hr : Continuous r)
    (q : ℝ) (m : E)
    (hsolve : m - q⁻¹ • covariance V v m = average (fun t => r t • V t)) :
    average (correctedVector V v q r m) = 0 := by
  have hh : Continuous (correctedScalar V v q r m) :=
    hr.add (((hV.sub continuous_const).inner continuous_const).div_const q)
  change average (fun t => q⁻¹ • (correctedScalar V v q r m t • V t - m)) = 0
  rw [average_const_smul,
    average_sub (f := fun t => correctedScalar V v q r m t • V t)
      (g := fun _ => m) (hh.smul hV) continuous_const, average_const,
    average_weighted_correctedScalar hV hv hr q m hsolve, sub_self, smul_zero]

omit [CompleteSpace E] in
theorem corrected_projection (V : Period → E)
    (v : E) {r : Period → ℝ} (hr : Continuous r) (hr0 : average r = 0)
    {q : ℝ} (hq : q ≠ 0) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) (m : E) :
    fluctuation (fun t => inner ℝ (V t) (correctedVector V v q r m t)) = r := by
  have he : ∀ t, inner ℝ (V t) (correctedVector V v q r m t) =
      r t - inner ℝ v m / q := by
    intro t
    simp only [correctedVector, correctedScalar, inner_smul_right, inner_sub_right,
      inner_sub_left, hcircle t]
    field_simp [hq]
    ring
  have hav : average (fun t => inner ℝ (V t) (correctedVector V v q r m t)) =
      -inner ℝ v m / q := by
    simp_rw [he]
    rw [average_sub hr continuous_const, average_const, hr0]
    ring
  funext t
  rw [fluctuation, he, hav]
  ring

/-- A continuous scalar function on the period circle cannot switch between
the two roots of a fixed square without taking intermediate values. -/
theorem constant_of_constant_square {a : Period → ℝ} (ha : Continuous a)
    (hsq : ∀ t, a t ^ 2 = a 0 ^ 2) : a = fun _ => a 0 := by
  have hfinite : (Set.range a).Finite := by
    apply ((Set.finite_singleton (-a 0)).insert (a 0)).subset
    rintro _ ⟨t, rfl⟩
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (sq_eq_sq_iff_eq_or_eq_neg.mp (hsq t))
  have hsub : (Set.range a).Subsingleton :=
    (isPreconnected_range ha).isDiscrete_iff_subsingleton.mp hfinite.isDiscrete
  funext t
  exact hsub ⟨t, rfl⟩ ⟨0, rfl⟩

theorem covariance_inner {V : Period → E} (hV : Continuous V) (v m : E) :
    inner ℝ (covariance V v m) m = average (fun t => (inner ℝ (V t - v) m) ^ 2) := by
  rw [covariance, ← average_inner_right
    (f := fun t => inner ℝ (V t - v) m • (V t - v))
    (((hV.sub continuous_const).inner continuous_const).smul (hV.sub continuous_const)) m]
  congr 1
  funext t
  rw [real_inner_smul_left, pow_two]

theorem average_centered_square {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) (m : E) :
    average (fun t => (inner ℝ (V t - v) m) ^ 2) =
      average (fun t => (inner ℝ (V t) m) ^ 2) - (inner ℝ v m) ^ 2 := by
  let a : Period → ℝ := fun t => inner ℝ (V t) m
  let c : ℝ := inner ℝ v m
  have ha : Continuous a := hV.inner continuous_const
  have hav : average a = c := (average_inner_right hV m).trans (congrArg (fun w => inner ℝ w m) hv)
  have he : (fun t => (inner ℝ (V t - v) m) ^ 2) =
      (fun t => a t ^ 2 - (2 * c) * a t + c ^ 2) := by
    funext t
    dsimp [a, c]
    rw [inner_sub_left]
    ring
  have hasq : Continuous (fun t => a t ^ 2) := by fun_prop
  have hscale : Continuous (fun t => (2 * c) * a t) := continuous_const.mul ha
  have hscaled : average (fun t => (2 * c) * a t) = (2 * c) * average a := by
    simpa only [smul_eq_mul] using average_const_smul (2 * c) a
  rw [he, average_add (f := fun t => a t ^ 2 - (2 * c) * a t)
      (g := fun _ => c ^ 2) (hasq.sub hscale) continuous_const,
    average_sub (f := fun t => a t ^ 2) (g := fun t => (2 * c) * a t)
      hasq hscale, hscaled, average_const, hav]
  change average (fun t => a t ^ 2) - (2 * c) * c + c ^ 2 =
    average (fun t => a t ^ 2) - c ^ 2
  ring

theorem meanOperator_kernel_trivial {V : Period → E} (hV : Continuous V)
    {v : E} (hv : average V = v) {q : ℝ} (hq : 0 < q)
    (hcircle : ∀ t, inner ℝ (V t) (V t) = q)
    (m : E) (hm : meanOperator V hV v q m = 0) : m = 0 := by
  let a : Period → ℝ := fun t => inner ℝ (V t) m
  let c : ℝ := inner ℝ v m
  let gap : Period → ℝ := fun t => q * inner ℝ m m - a t ^ 2
  have ha : Continuous a := hV.inner continuous_const
  have hgap : Continuous gap := continuous_const.sub (ha.pow 2)
  have hgapnonneg : ∀ t, 0 ≤ gap t := by
    intro t
    have hcauchy := real_inner_mul_inner_self_le (V t) m
    rw [hcircle t] at hcauchy
    dsimp [gap, a]
    nlinarith only [hcauchy]
  have hmean : average gap = q * inner ℝ m m - average (fun t => a t ^ 2) := by
    exact (average_sub (f := fun _ => q * inner ℝ m m)
      (g := fun t => a t ^ 2) continuous_const (by fun_prop)).trans (by rw [average_const])
  have hkernel : inner ℝ (covariance V v m) m = q * inner ℝ m m := by
    have he := congrArg (fun w => inner ℝ w m) hm
    simp only [meanOperator_apply, inner_sub_left, real_inner_smul_left, inner_zero_left] at he
    have hi : q⁻¹ * inner ℝ (covariance V v m) m = inner ℝ m m := by linarith
    have he' := congrArg (fun x : ℝ => q * x) hi
    simpa only [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul] using he'
  have hvariance := (covariance_inner hV v m).trans (average_centered_square hV hv m)
  have hsum : average gap + c ^ 2 = 0 := by
    dsimp [c, a] at hmean ⊢
    linarith [hmean, hkernel, hvariance]
  have hnonneg : 0 ≤ average gap := integral_nonneg hgapnonneg
  have havzero : average gap = 0 := by nlinarith [sq_nonneg c]
  have hczero : c = 0 := by nlinarith [sq_nonneg c]
  have hae : gap =ᵐ[AddCircle.haarAddCircle] 0 :=
    (integral_eq_zero_iff_of_nonneg hgapnonneg (integrable_of_continuous hgap)).mp havzero
  have hgapzero : gap = 0 :=
    (hgap.ae_eq_iff_eq AddCircle.haarAddCircle continuous_zero).mp hae
  have hsq : ∀ t, a t ^ 2 = q * inner ℝ m m := by
    intro t
    have h := congrFun hgapzero t
    dsimp [gap] at h
    linarith
  have haconst : a = fun _ => a 0 :=
    constant_of_constant_square ha (fun t => (hsq t).trans (hsq 0).symm)
  have hav : average a = c :=
    (average_inner_right hV m).trans (congrArg (fun w => inner ℝ w m) hv)
  have ha0 : a 0 = 0 := by
    rw [haconst, average_const, hczero] at hav
    exact hav
  have hmm : inner ℝ m m = 0 := by
    have he := hsq 0
    rw [ha0, zero_pow (by decide : 2 ≠ 0)] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hq.ne'
  exact (inner_self_eq_zero.mp hmm)

end ClosedSurfaceR4.CovarianceCorrector

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicPrimitive
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The normalized periodic antiderivative used by the finite periodic expansion.
The primitive is constructed by integration, followed by subtraction of its
mean.  The period is one, matching `UnitAddCircle`.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem rawPrimitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (rawPrimitive f) (f x) x :=
  (hf.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem rawPrimitive_continuous {f : ℝ → E} (hf : Continuous f) :
    Continuous (rawPrimitive f) :=
  (show Differentiable ℝ (rawPrimitive f) from
    fun x => (rawPrimitive_hasDerivAt hf x).differentiableAt).continuous

theorem primitive_hasDerivAt {f : ℝ → E} (hf : Continuous f) (x : ℝ) :
    HasDerivAt (primitive f) (f x) x :=
  (rawPrimitive_hasDerivAt hf x).sub_const _

theorem primitive_mean_zero {f : ℝ → E} (hf : Continuous f) :
    (∫ t in 0..1, primitive f t) = 0 := by
  unfold primitive
  rw [intervalIntegral.integral_sub
    ((rawPrimitive_continuous hf).intervalIntegrable 0 1) intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, one_smul, sub_self]

end ClosedSurfaceR4.PeriodicPrimitive

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalParameterIntegral
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parameter integration on an open admissible domain, localized by a smooth cutoff. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology

universe u

namespace ClosedSurfaceR4.SmoothParameterIntegral

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Differentiation under the integral at an admissible parameter. -/
theorem hasFDerivAt_integral_on {F : P × ℝ → E} {S : Set P} (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ F (S ×ˢ univ)) (a b : ℝ) {p : P} (hp : p ∈ S) :
    HasFDerivAt (fun q => ∫ t in a..b, F (q, t))
      (∫ t in a..b, partialDerivative F (p, t)) p := by
  obtain ⟨G, hG, he⟩ := exists_smooth_extension_near hS hF hp
  have hd : (fun t => partialDerivative G (p, t)) =
      fun t => partialDerivative F (p, t) := by
    funext t
    have he' : G =ᶠ[𝓝 (p, t)] F := by
      filter_upwards [(continuous_fst.continuousAt :
        Tendsto Prod.fst (𝓝 (p, t)) (𝓝 p)).eventually he] with z hz
      exact hz z.2
    simp only [partialDerivative, he'.fderiv_eq]
  have h := hasFDerivAt_integral hG a b p
  rw [hd] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [he] with q hq
  exact intervalIntegral.integral_congr (fun t _ => (hq t).symm)

end ClosedSurfaceR4.SmoothParameterIntegral

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCalculus
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.averageCLM_apply _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.periodicBilinear_apply _root_.OAI.ClosedSurfaceR4.CovarianceCorrector.weightedAverage_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.ofLocal_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.zero_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
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

lemma angleOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F p (s : Period)) (angleOn F S hS hF p (t : Period)) t := by
  rw [angleOn, bundleOn_apply _ _ _ _ _ hp]
  exact angle_hasDerivAt hS hF hp t

lemma angleOn_zero_at (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {p : P} (hp : p ∈ S) (hz : F p = 0) : angleOn F S hS hF p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro t
  have hd := angleOn_hasDerivAt F S hS hF hp t
  rw [hz] at hd
  exact hd.unique (hasDerivAt_const t (0 : E))

lemma slowOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (v : P) {p : P} (hp : p ∈ S) (t : ℝ) :
    slowOn F S hS hF v p (t : Period) =
      slowDerivative (fun z : P × ℝ => F z.1 (z.2 : Period)) v (p, t) :=
  bundleOn_apply _ _ _ _ _ hp t


lemma slowOn_zero_on (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    {O : Set P} (hO : IsOpen O) (hz : ∀ p ∈ O, F p = 0) (v : P)
    {p : P} (hp : p ∈ S) (hpO : p ∈ O) : slowOn F S hS hF v p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro t
  rw [slowOn_apply F S hS hF v hp, ← fderiv_slice hS hF hp]
  have he : (fun q => F q (t : Period)) =ᶠ[𝓝 p] fun _ => (0 : E) := by
    filter_upwards [hO.mem_nhds hpO] with q hq
    rw [hz q hq]
    rfl
  rw [he.fderiv_eq, fderiv_const_apply, zero_apply]
  rfl

variable [FiniteDimensional ℝ P] [CompleteSpace E]

lemma primitiveOn_apply (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    primitiveOn F S hS hF hm p (t : Period) =
      PeriodicPrimitive.primitive (fun s => F p (s : Period)) t :=
  bundleOn_apply _ _ _ _ _ hp t

lemma primitiveOn_hasDerivAt (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (t : ℝ) :
    HasDerivAt (fun s : ℝ => primitiveOn F S hS hF hm p (s : Period)) (F p (t : Period)) t := by
  simp only [primitiveOn_apply F S hS hF hm hp]
  exact PeriodicPrimitive.primitive_hasDerivAt ((F p).continuous.comp (AddCircle.continuous_mk' 1)) t

lemma primitiveOn_mean_zero (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) :
    average (primitiveOn F S hS hF hm p) = 0 := by
  rw [CovarianceCorrector.average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [primitiveOn_apply F S hS hF hm hp]
  exact PeriodicPrimitive.primitive_mean_zero
    ((F p).continuous.comp (AddCircle.continuous_mk' 1))

lemma primitiveOn_zero_at (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) {p : P} (hp : p ∈ S) (hz : F p = 0) :
    primitiveOn F S hS hF hm p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro t
  rw [primitiveOn_apply F S hS hF hm hp, hz]
  exact PeriodicPrimitive.primitive_zero t

omit [CompleteSpace E] in
lemma slowOn_mean_zero (F : P → C(Period, E)) (S : Set P) (hS : IsOpen S)
    (hF : ContDiffOn ℝ ∞ (fun z : P × ℝ => F z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hm : ∀ p ∈ S, average (F p) = 0) (v : P) {p : P} (hp : p ∈ S) :
    average (slowOn F S hS hF v p) = 0 := by
  let f : P × ℝ → E := fun z => F z.1 (z.2 : Period)
  have hzero : (fun q => ∫ t in 0..1, f (q, t)) =ᶠ[𝓝 p] fun _ => (0 : E) := by
    filter_upwards [hS.mem_nhds hp] with q hq
    exact (PeriodicPrimitive.integral_lift_eq_haar (F q)).trans (hm q hq)
  have hd := (SmoothParameterIntegral.hasFDerivAt_integral_on hS hF 0 1 hp).fderiv
  change fderiv ℝ (fun q => ∫ t in 0..1, f (q, t)) p = _ at hd
  rw [hzero.fderiv_eq, fderiv_const_apply] at hd
  have he := congrArg (fun L : P →L[ℝ] E => L v) hd.symm
  have hi := ContinuousLinearMap.intervalIntegral_apply (μ := volume)
    (φ := fun t => SmoothParameterIntegral.partialDerivative f (p, t))
    ((smooth_slice hS (hF.fderiv_of_isOpen (hS.prod isOpen_univ) (by simp)) hp).continuous
      |>.clm_comp continuous_const |>.intervalIntegrable 0 1) v
  rw [CovarianceCorrector.average, ← PeriodicPrimitive.integral_lift_eq_haar]
  simp only [slowOn_apply F S hS hF v hp]
  exact hi.symm.trans he

end ClosedSurfaceR4.LocalPeriodicCalculus

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialIntegral
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.eval_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_fluct _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_liftOperator _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_neg _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_sub _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Angular derivatives, averaging, and normalized primitives act only on
smooth low-jet coefficients, preserving polynomial jet order and scale loss. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open SmoothPeriodicCalculus

namespace Expression

lemma eval_slice_smooth {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) :
    ContDiff ℝ ∞ (fun t => e.eval G (p, t)) := by
  induction e with
  | coeff c => exact LocalPeriodicCalculus.smooth_slice hO he hp
  | atom w a e ih =>
    change ContDiff ℝ ∞ (fun t => jet G w a p * e.eval G (p, t))
    exact contDiff_const.mul (ih he)
  | add e f ihe ihf => exact (ihe he.1).add (ihf he.2)

lemma smoothCoeffs_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.angle.SmoothCoeffs O :=
  smoothCoeffs_map e _ (fun _ hc => LocalPeriodicCalculus.angle_smooth hO hc) he

lemma smoothCoeffs_mean {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.mean.SmoothCoeffs O := by
  apply smoothCoeffs_map e _ _ he
  intro c hc
  exact (SmoothParameterIntegral.contDiffOn_integral hO hc 0 1).comp contDiffOn_fst
    (fun _ hz => hz.1)

lemma smoothCoeffs_primitive {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.primitive.SmoothCoeffs O :=
  smoothCoeffs_map e _ (fun _ hc => PeriodicPrimitive.contDiffOn_primitive_joint hO hc) he

lemma eval_angle {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.angle.eval G (p, t) = deriv (fun s => e.eval G (p, s)) t := by
  induction e with
  | coeff c => exact (LocalPeriodicCalculus.angle_hasDerivAt hO he hp t).deriv.symm
  | atom w a e ih =>
    change jet G w a p * e.angle.eval G (p, t) =
      deriv (fun s => jet G w a p * e.eval G (p, s)) t
    rw [deriv_const_mul _ ((eval_slice_smooth hO (e := e) he G hp).differentiable (by simp) t),
      ih he]
  | add e f ihe ihf =>
    change e.angle.eval G (p, t) + f.angle.eval G (p, t) =
      deriv (fun s => e.eval G (p, s) + f.eval G (p, s)) t
    rw [deriv_fun_add ((eval_slice_smooth hO he.1 G hp).differentiable (by simp) t)
      ((eval_slice_smooth hO he.2 G hp).differentiable (by simp) t), ihe he.1, ihf he.2]

lemma eval_mean {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.mean.eval G (p, t) = ∫ s in 0..1, e.eval G (p, s) := by
  induction e with
  | coeff c => rfl
  | atom w a e ih =>
    change jet G w a p * e.mean.eval G (p, t) = ∫ s in 0..1, jet G w a p * e.eval G (p, s)
    rw [intervalIntegral.integral_const_mul, ih he]
  | add e f ihe ihf =>
    change e.mean.eval G (p, t) + f.mean.eval G (p, t) =
      ∫ s in 0..1, (e.eval G (p, s) + f.eval G (p, s))
    rw [intervalIntegral.integral_add
      ((eval_slice_smooth hO he.1 G hp).continuous.intervalIntegrable 0 1)
      ((eval_slice_smooth hO he.2 G hp).continuous.intervalIntegrable 0 1), ihe he.1, ihf he.2]

lemma normalizedPrimitive_const_mul (c : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    PeriodicPrimitive.primitive (fun s => c * f s) t = c * PeriodicPrimitive.primitive f t := by
  simp only [PeriodicPrimitive.primitive, PeriodicPrimitive.rawPrimitive,
    intervalIntegral.integral_const_mul, mul_sub]

lemma normalizedPrimitive_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    PeriodicPrimitive.primitive (fun s => f s + g s) t =
      PeriodicPrimitive.primitive f t + PeriodicPrimitive.primitive g t := by
  have hi (s : ℝ) : PeriodicPrimitive.rawPrimitive (fun x => f x + g x) s =
      PeriodicPrimitive.rawPrimitive f s + PeriodicPrimitive.rawPrimitive g s :=
    intervalIntegral.integral_add (hf.intervalIntegrable 0 s) (hg.intervalIntegrable 0 s)
  simp only [PeriodicPrimitive.primitive, hi]
  rw [intervalIntegral.integral_add
    ((PeriodicPrimitive.rawPrimitive_continuous hf).intervalIntegrable 0 1)
    ((PeriodicPrimitive.rawPrimitive_continuous hg).intervalIntegrable 0 1)]
  ring

lemma eval_primitive {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.primitive.eval G (p, t) = PeriodicPrimitive.primitive (fun s => e.eval G (p, s)) t := by
  induction e with
  | coeff c => rfl
  | atom w a e ih =>
    change jet G w a p * e.primitive.eval G (p, t) =
      PeriodicPrimitive.primitive (fun s => jet G w a p * e.eval G (p, s)) t
    rw [normalizedPrimitive_const_mul, ih he]
  | add e f ihe ihf =>
    change e.primitive.eval G (p, t) + f.primitive.eval G (p, t) =
      PeriodicPrimitive.primitive (fun s => e.eval G (p, s) + f.eval G (p, s)) t
    rw [normalizedPrimitive_add (eval_slice_smooth hO he.1 G hp).continuous
      (eval_slice_smooth hO he.2 G hp).continuous, ihe he.1, ihf he.2]

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialLinear
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Linear operators in the angular variable preserve higher-jet polynomials.
This includes operators whose coefficients depend smoothly on the second jet. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

lemma smoothCoeffs_liftOperator {O : Set LowJet} {T : LowJet → (ℝ → ℝ) → ℝ → ℝ}
    (hT : ∀ c : LowJet × ℝ → ℝ, ContDiffOn ℝ ∞ c (O ×ˢ Set.univ) →
      ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => T z.1 (fun t => c (z.1, t)) z.2)
        (O ×ˢ Set.univ)) {e : Expression} (he : e.SmoothCoeffs O) :
    (e.liftOperator T).SmoothCoeffs O := smoothCoeffs_map e _ hT he

/-- This uses actual operator linearity, not an assumed polynomial representation. -/
lemma eval_liftOperator {O : Set LowJet} (hO : IsOpen O)
    (T : LowJet → (ℝ → ℝ) → ℝ → ℝ)
    (hadd : ∀ Q ∈ O, ∀ f g : ℝ → ℝ, Continuous f → Continuous g → ∀ t,
      T Q (fun s => f s + g s) t = T Q f t + T Q g t)
    (hsmul : ∀ Q ∈ O, ∀ a : ℝ, ∀ f : ℝ → ℝ, ∀ t,
      T Q (fun s => a * f s) t = a * T Q f t)
    {e : Expression} (he : e.SmoothCoeffs O) (G : Base → Space)
    {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    (e.liftOperator T).eval G (p, t) = T (lowJet G p) (fun s => e.eval G (p, s)) t := by
  induction e with
  | coeff c => rfl
  | atom w a e ih =>
    change jet G w a p * (e.liftOperator T).eval G (p, t) =
      T (lowJet G p) (fun s => jet G w a p * e.eval G (p, s)) t
    rw [hsmul _ hp, ih he]
  | add e f ihe ihf =>
    change (e.liftOperator T).eval G (p, t) + (f.liftOperator T).eval G (p, t) =
      T (lowJet G p) (fun s => e.eval G (p, s) + f.eval G (p, s)) t
    rw [hadd _ hp _ _ (eval_slice_smooth hO he.1 G hp).continuous
      (eval_slice_smooth hO he.2 G hp).continuous, ihe he.1, ihf he.2]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CovarianceParameter
attribute [-instance] _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Smooth parameter dependence of the actual finite covariance solve.  Averaging
is a bounded linear map on continuous periodic functions; the covariance is
a quadratic map on that Banach space.  Thus no regularity assumption on the
inverse matrix is needed.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

variable {E P : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem covarianceCLM_apply (V : C(Period, E)) (m : E) :
    covarianceCLM V m = covariance V (average V) m := by
  unfold covarianceCLM
  rw [averageCLM_apply]
  change (∫ t, periodicBilinear (InnerProductSpace.rankOne ℝ)
    (centeredPeriodic V) (centeredPeriodic V) t ∂AddCircle.haarAddCircle) m = _
  rw [ContinuousLinearMap.integral_apply (integrable_of_continuous
    (periodicBilinear (InnerProductSpace.rankOne ℝ)
      (centeredPeriodic V) (centeredPeriodic V)).continuous)]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem meanCLM_apply (V : C(Period, E)) (q : ℝ) (m : E) :
    meanCLM V q m = m - q⁻¹ • covariance V (average V) m := by
  simp only [meanCLM, sub_apply, ContinuousLinearMap.id_apply,
    smul_apply, covarianceCLM_apply]

theorem meanCLM_isInvertible {V : C(Period, E)} {q : ℝ} (hq : 0 < q)
    (hcircle : ∀ t, inner ℝ (V t) (V t) = q) : (meanCLM V q).IsInvertible := by
  have hinj : Function.Injective (meanCLM V q) := by
    intro m n he
    apply sub_eq_zero.mp
    apply meanOperator_kernel_trivial V.continuous rfl hq hcircle
    change (m - n) - q⁻¹ • covariance V (average V) (m - n) = 0
    rw [← meanCLM_apply, map_sub, he, sub_self]
  have hsurj : Function.Surjective (meanCLM V q) :=
    LinearMap.surjective_of_injective (f := (meanCLM V q).toLinearMap) hinj
  refine ⟨(LinearEquiv.ofBijective (meanCLM V q).toLinearMap ⟨hinj, hsurj⟩).toContinuousLinearEquiv, ?_⟩
  rfl

theorem covarianceSolution_equation {V : C(Period, E)} (r : C(Period, ℝ))
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) :
    covarianceSolution V r q - q⁻¹ • covariance V (average V) (covarianceSolution V r q) =
      average (fun t => r t • V t) := by
  rw [← meanCLM_apply]
  exact (meanCLM_isInvertible hq hcircle).self_apply_inverse _

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalCovarianceParameter
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The covariance correction is smooth on the open admissible geometric domain. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma contDiffOn_covarianceCLM_joint {V : P → C(Period, E)} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p => covarianceCLM (V p)) S := by
  have hc := hV.sub ((contDiffOn_average_joint hS hV).comp contDiffOn_fst (fun _ hz => hz.1))
  rw [contDiffOn_clm_apply]
  intro m
  simp_rw [covarianceCLM_apply]
  have hi := SmoothParameterIntegral.contDiffOn_integral hS
    ((hc.inner ℝ (contDiffOn_const (c := m))).smul hc) 0 1
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact (PeriodicPrimitive.integral_lift_eq_haar
    (fun t => inner ℝ (V p t - average (V p)) m • (V p t - average (V p)))).symm

omit [FiniteDimensional ℝ E] in
lemma contDiffOn_weightedAverage_joint {V : P → C(Period, E)} {r : P → C(Period, ℝ)}
    {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hr : ContDiffOn ℝ ∞ (fun z : P × ℝ => r z.1 (z.2 : Period)) (S ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p => weightedAverage (V p) (r p)) S := by
  have hi := SmoothParameterIntegral.contDiffOn_integral hS (hr.smul hV) 0 1
  convert hi using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  exact (PeriodicPrimitive.integral_lift_eq_haar (fun t => r p t • V p t)).symm

lemma contDiffOn_covarianceSolution_joint {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hr : ContDiffOn ℝ ∞ (fun z : P × ℝ => r z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q S) (hqpos : ∀ p ∈ S, 0 < q p)
    (hcircle : ∀ p ∈ S, ∀ t, inner ℝ (V p t) (V p t) = q p) :
    ContDiffOn ℝ ∞ (fun p => covarianceSolution (V p) (r p) (q p)) S := by
  have hM : ContDiffOn ℝ ∞ (fun p => meanCLM (V p) (q p)) S :=
    contDiffOn_const.sub ((hq.inv (fun p hp => (hqpos p hp).ne')).smul
      (contDiffOn_covarianceCLM_joint hS hV))
  have hi : ContDiffOn ℝ ∞ (fun p => (meanCLM (V p) (q p)).inverse) S := by
    apply hS.contDiffOn_iff.mpr
    intro p hp
    exact (meanCLM_isInvertible (hqpos p hp) (hcircle p hp)).contDiffAt_map_inverse.comp p
      (hM.contDiffAt (hS.mem_nhds hp))
  exact hi.clm_apply (contDiffOn_weightedAverage_joint hS hV hr)

lemma contDiffOn_parameterCorrector_joint {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} {S : Set P} (hS : IsOpen S)
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hr : ContDiffOn ℝ ∞ (fun z : P × ℝ => r z.1 (z.2 : Period)) (S ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q S) (hqpos : ∀ p ∈ S, 0 < q p)
    (hcircle : ∀ p ∈ S, ∀ t, inner ℝ (V p t) (V p t) = q p) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => parameterCorrector V r q z.1 (z.2 : Period))
      (S ×ˢ Set.univ) := by
  have hm : ContDiffOn ℝ ∞ (fun z : P × ℝ =>
      covarianceSolution (V z.1) (r z.1) (q z.1)) (S ×ˢ Set.univ) :=
    (contDiffOn_covarianceSolution_joint hS hV hr hq hqpos hcircle).comp
    contDiffOn_fst (fun _ hz => hz.1)
  have hv : ContDiffOn ℝ ∞ (fun z : P × ℝ => average (V z.1)) (S ×ˢ Set.univ) :=
    (contDiffOn_average_joint hS hV).comp contDiffOn_fst (fun _ hz => hz.1)
  have hi : ContDiffOn ℝ ∞ (fun z : P × ℝ => (q z.1)⁻¹) (S ×ˢ Set.univ) :=
    (hq.comp contDiffOn_fst (fun _ hz => hz.1)).inv (fun z hz => (hqpos z.1 hz.1).ne')
  have hs : ContDiffOn ℝ ∞ (fun z : P × ℝ =>
      correctedScalar (V z.1) (average (V z.1)) (q z.1) (r z.1)
        (covarianceSolution (V z.1) (r z.1) (q z.1)) (z.2 : Period)) (S ×ˢ Set.univ) := by
    simpa only [correctedScalar, div_eq_mul_inv] using
      hr.add (((hV.sub hv).inner ℝ hm).mul hi)
  exact hi.smul ((hs.smul hV).sub hm)

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_CovarianceRealOperator
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual covariance correction acting on real-parameter forcing.
This form exposes linearity and does not require separate periodicity proofs
for the individual coefficients of a jet polynomial. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.CovarianceCorrector

variable {E P : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma realMeanSolution_add (V : C(Period, E)) (q : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    realMeanSolution V q (fun t => f t + g t) =
      realMeanSolution V q f + realMeanSolution V q g := by
  unfold realMeanSolution realMoment
  simp only [add_smul]
  have hfi : IntervalIntegrable (fun t : ℝ => f t • V (t : Period)) volume 0 1 :=
    (hf.smul (V.continuous.comp (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  have hgi : IntervalIntegrable (fun t : ℝ => g t • V (t : Period)) volume 0 1 :=
    (hg.smul (V.continuous.comp (AddCircle.continuous_mk' 1))).intervalIntegrable 0 1
  rw [intervalIntegral.integral_add hfi hgi, map_add]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma realMeanSolution_smul (V : C(Period, E)) (q a : ℝ) (f : ℝ → ℝ) :
    realMeanSolution V q (fun t => a * f t) = a • realMeanSolution V q f := by
  unfold realMeanSolution realMoment
  simp only [mul_smul, intervalIntegral.integral_smul, map_smul]

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma realCorrector_add (V : C(Period, E)) (q : ℝ) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    realCorrector V q (fun s => f s + g s) t = realCorrector V q f t + realCorrector V q g t := by
  simp only [realCorrector, realMeanSolution_add V q hf hg, inner_add_right, add_div]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma realCorrector_smul (V : C(Period, E)) (q a : ℝ) (f : ℝ → ℝ) (t : ℝ) :
    realCorrector V q (fun s => a * f s) t = a • realCorrector V q f t := by
  simp only [realCorrector, realMeanSolution_smul, inner_smul_right]
  have ha : a * f t + a * inner ℝ (V (t : Period) - average V) (realMeanSolution V q f) / q =
      a * (f t + inner ℝ (V (t : Period) - average V) (realMeanSolution V q f) / q) := by ring
  rw [ha]
  module

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup P]
  [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- Agreement with the covariance correction already used in the periodic solver. -/
lemma realCorrector_eq_parameterCorrector (V : P → C(Period, E)) (q : P → ℝ)
    (r : P → C(Period, ℝ)) (p : P) (t : ℝ) :
    realCorrector (V p) (q p) (fun s => r p (s : Period)) t =
      parameterCorrector V r q p (t : Period) := by
  have hm : realMoment (V p) (fun s => r p (s : Period)) = weightedAverage (V p) (r p) := by
    exact PeriodicPrimitive.integral_lift_eq_haar (fun s => r p s • V p s)
  simp only [realCorrector, realMeanSolution, hm, parameterCorrector,
    correctedVector, correctedScalar, covarianceSolution]

lemma contDiffOn_realMeanSolution {O : Set P} (hO : IsOpen O)
    {V : P → C(Period, E)} {q : P → ℝ} {c : P × ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun p => realMeanSolution (V p) (q p) (fun t => c (p, t))) O := by
  have hM : ContDiffOn ℝ ∞ (fun p => meanCLM (V p) (q p)) O :=
    contDiffOn_const.sub ((hq.inv (fun p hp => (hqpos p hp).ne')).smul
      (contDiffOn_covarianceCLM_joint hO hV))
  have hi : ContDiffOn ℝ ∞ (fun p => (meanCLM (V p) (q p)).inverse) O := by
    apply hO.contDiffOn_iff.mpr
    intro p hp
    exact (meanCLM_isInvertible (hqpos p hp) (hcircle p hp)).contDiffAt_map_inverse.comp p
      (hM.contDiffAt (hO.mem_nhds hp))
  exact hi.clm_apply (SmoothParameterIntegral.contDiffOn_integral hO (hc.smul hV) 0 1)

lemma contDiffOn_realCorrector {O : Set P} (hO : IsOpen O)
    {V : P → C(Period, E)} {q : P → ℝ} {c : P × ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (fun z : P × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (hc : ContDiffOn ℝ ∞ c (O ×ˢ Set.univ)) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ => realCorrector (V z.1) (q z.1)
      (fun t => c (z.1, t)) z.2) (O ×ˢ Set.univ) := by
  have hm : ContDiffOn ℝ ∞ (fun z : P × ℝ =>
      realMeanSolution (V z.1) (q z.1) (fun t => c (z.1, t))) (O ×ˢ Set.univ) :=
    (contDiffOn_realMeanSolution hO hV hq hqpos hcircle hc).comp
    contDiffOn_fst (fun _ hz => hz.1)
  have hv : ContDiffOn ℝ ∞ (fun z : P × ℝ => average (V z.1)) (O ×ˢ Set.univ) :=
    (contDiffOn_average_joint hO hV).comp contDiffOn_fst (fun _ hz => hz.1)
  have hq' : ContDiffOn ℝ ∞ (fun z : P × ℝ => q z.1) (O ×ˢ Set.univ) :=
    hq.comp contDiffOn_fst (fun _ hz => hz.1)
  have hi := hq'.inv (fun z hz => (hqpos z.1 hz.1).ne')
  exact hi.smul (((hc.add (((hV.sub hv).inner ℝ hm).div hq'
    (fun z hz => (hqpos z.1 hz.1).ne'))).smul hV).sub hm)

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialCovariance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual covariance inversion preserves finite polynomial dependence on
higher jets. Its inverse matrix depends only on the low-jet geometric data. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression
open CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

lemma smoothCoeffs_covariance {O : Set LowJet} (hO : IsOpen O)
    {V : LowJet → C(Period, E)} {q : LowJet → ℝ}
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (L : E →L[ℝ] ℝ) {e : Expression} (he : e.SmoothCoeffs O) :
    (e.covariance V q L).SmoothCoeffs O := by
  apply smoothCoeffs_liftOperator _ he
  intro c hc
  exact L.contDiff.comp_contDiffOn (contDiffOn_realCorrector hO hV hq hqpos hcircle hc)

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma eval_covariance {O : Set LowJet} (hO : IsOpen O)
    (V : LowJet → C(Period, E)) (q : LowJet → ℝ) (L : E →L[ℝ] ℝ)
    {e : Expression} (he : e.SmoothCoeffs O) (G : Base → Space)
    {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    (e.covariance V q L).eval G (p, t) =
      L (realCorrector (V (lowJet G p)) (q (lowJet G p)) (fun s => e.eval G (p, s)) t) := by
  apply eval_liftOperator hO _ _ _ he G hp t
  · intro Q _ f g hf hg s
    rw [realCorrector_add _ _ hf hg, map_add]
  · intro Q _ a f s
    rw [realCorrector_smul, map_smul, smul_eq_mul]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialOperations
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.Expression

lemma smoothCoeffs_neg {O : Set LowJet} {e : Expression} (he : e.SmoothCoeffs O) :
    e.neg.SmoothCoeffs O := smoothCoeffs_map e _ (fun _ hc => hc.neg) he

lemma smoothCoeffs_sub {O : Set LowJet} {e f : Expression}
    (he : e.SmoothCoeffs O) (hf : f.SmoothCoeffs O) : (e.sub f).SmoothCoeffs O :=
  ⟨he, smoothCoeffs_neg hf⟩

lemma smoothCoeffs_fluct {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) : e.fluct.SmoothCoeffs O :=
  smoothCoeffs_sub he (smoothCoeffs_mean hO he)

lemma eval_fluct {O : Set LowJet} (hO : IsOpen O) {e : Expression}
    (he : e.SmoothCoeffs O) (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    e.fluct.eval G (p, t) = e.eval G (p, t) - ∫ s in (0 : ℝ)..1, e.eval G (p, s) := by
  rw [fluct, eval_sub, eval_mean hO he G hp]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PeriodicCorrector
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
The two components of the finite periodic corrector: the explicit solve in
span(Y,C), and integration of the covariance correction in its orthogonal
complement.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCorrector

open CovarianceCorrector PeriodicCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma spanSolve_pairings (Y C : E) (hD : gramDet Y C ≠ 0) (a : ℝ × ℝ) :
    inner ℝ Y (spanSolve Y C a) = a.1 ∧
      inner ℝ C (spanSolve Y C a) = a.2 := by
  change inner ℝ Y (_ • Y + _ • C) = a.1 ∧
    inner ℝ C (_ • Y + _ • C) = a.2
  have hc : inner ℝ C Y = inner ℝ Y C := (real_inner_comm C Y).symm
  simp only [inner_add_right, real_inner_smul_right, hc]
  constructor
  · calc
      _ = a.1 * gramDet Y C / gramDet Y C := by unfold gramDet; ring
      _ = a.1 := mul_div_cancel_right₀ _ hD
  · calc
      _ = a.2 * gramDet Y C / gramDet Y C := by unfold gramDet; ring
      _ = a.2 := mul_div_cancel_right₀ _ hD

lemma average_spanSolve (Y C : E) {H K : Period → ℝ}
    (hH : Continuous H) (hK : Continuous K)
    (hmH : average H = 0) (hmK : average K = 0) :
    average (fun t => spanSolve Y C (H t, K t)) = 0 := by
  have hi := integrable_of_continuous (hH.prodMk hK)
  have he := (spanSolve Y C).integral_comp_comm hi
  have hm : (∫ t, (H t, K t) ∂AddCircle.haarAddCircle) = (0, 0) := by
    apply Prod.ext
    · have hx := (ContinuousLinearMap.fst ℝ ℝ ℝ).integral_comp_comm hi
      change (∫ t, H t ∂AddCircle.haarAddCircle) =
        (∫ t, (H t, K t) ∂AddCircle.haarAddCircle).1 at hx
      exact hx.symm.trans hmH
    · have hx := (ContinuousLinearMap.snd ℝ ℝ ℝ).integral_comp_comm hi
      change (∫ t, K t ∂AddCircle.haarAddCircle) =
        (∫ t, (H t, K t) ∂AddCircle.haarAddCircle).2 at hx
      exact hx.symm.trans hmK
  change (∫ t, spanSolve Y C (H t, K t) ∂AddCircle.haarAddCircle) = 0
  rw [he, hm]
  exact (spanSolve Y C).map_zero

lemma average_fluctuation {r : Period → ℝ} (hr : Continuous r) :
    average (fluctuation r) = 0 := by
  change CovarianceCorrector.average (fun t => r t - CovarianceCorrector.average r) = 0
  rw [average_sub hr continuous_const, CovarianceCorrector.average_const, sub_self]

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_PeriodicSubspace
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit covariance and primitive operations preserve a fixed
subspace at each parameter value; no choice of a moving frame is required. -/

noncomputable section
open MeasureTheory

namespace ClosedSurfaceR4.CovarianceCorrector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma average_mem_submodule (P : Submodule ℝ E) {f : Period → E}
    (hf : Continuous f) (hm : ∀ t, f t ∈ P) : average f ∈ P :=
  P.convex.integral_mem P.closed_of_finiteDimensional
    (Filter.Eventually.of_forall hm) (integrable_of_continuous hf)

lemma covariance_mem_submodule (P : Submodule ℝ E) {V : Period → E}
    (hV : Continuous V) (hmem : ∀ t, V t ∈ P) {v : E} (hv : v ∈ P) (m : E) :
    covariance V v m ∈ P := by
  apply average_mem_submodule P
  · exact ((hV.sub continuous_const).inner continuous_const).smul (hV.sub continuous_const)
  · intro t
    exact P.smul_mem _ (P.sub_mem (hmem t) hv)

/-- The equation for m forces m into the velocity plane, since both terms
on its right side belong to that plane. -/
lemma covarianceSolution_mem_submodule (P : Submodule ℝ E)
    (V : C(Period, E)) (r : C(Period, ℝ)) (hmem : ∀ t, V t ∈ P)
    {q : ℝ} (hq : 0 < q) (hcircle : ∀ t, inner ℝ (V t) (V t) = q) :
    covarianceSolution V r q ∈ P := by
  have hv := average_mem_submodule P V.continuous hmem
  have hc := covariance_mem_submodule P V.continuous hmem hv (covarianceSolution V r q)
  have hr : average (fun t => r t • V t) ∈ P :=
    average_mem_submodule P (r.continuous.smul V.continuous)
      (fun t => P.smul_mem _ (hmem t))
  have he := covarianceSolution_equation r hq hcircle
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  exact P.add_mem hr (P.smul_mem _ hc)

end ClosedSurfaceR4.CovarianceCorrector

namespace ClosedSurfaceR4.PeriodicPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma intervalIntegral_mem_submodule (P : Submodule ℝ E) {f : ℝ → E}
    (hf : Continuous f) (hm : ∀ t, f t ∈ P) (a b : ℝ) :
    (∫ t in a..b, f t) ∈ P := by
  let g : ℝ → P := fun t => ⟨f t, hm t⟩
  have hg : Continuous g := hf.subtype_mk _
  change (∫ t in a..b, P.subtypeL (g t)) ∈ P
  rw [P.subtypeL.intervalIntegral_comp_comm (hg.intervalIntegrable a b)]
  exact (∫ t in a..b, g t).property

lemma primitive_mem_submodule (P : Submodule ℝ E) {f : ℝ → E}
    (hf : Continuous f) (hm : ∀ t, f t ∈ P) (x : ℝ) : primitive f x ∈ P := by
  apply P.sub_mem (intervalIntegral_mem_submodule P hf hm 0 x)
  exact intervalIntegral_mem_submodule P (rawPrimitive_continuous hf)
    (fun t => intervalIntegral_mem_submodule P hf hm 0 t) 0 1

end ClosedSurfaceR4.PeriodicPrimitive

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_IntegratedCovariance
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal component of the periodic correction, including its actual
primitive, parameter smoothness, normalization, and support preservation. -/

noncomputable section
open MeasureTheory
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

open PeriodicPrimitive

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [FiniteDimensional ℝ E] in
/-- A zero prescribed fluctuation gives the zero explicit corrector. -/
theorem parameterCorrector_zero {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} {p : P}
    (hr : ∀ t, r p t = 0) (t : Period) : parameterCorrector V r q p t = 0 := by
  have hz : r p = 0 := by ext s; exact hr s
  have hm : covarianceSolution (V p) (r p) (q p) = 0 := by
    rw [covarianceSolution]
    have hw : weightedAverage (V p) (r p) = 0 := by
      rw [weightedAverage_apply]
      simp only [hr, zero_smul]
      exact average_const 0
    rw [hw, map_zero]
  simp only [parameterCorrector, correctedVector, correctedScalar, hm, hr,
    inner_zero_right, zero_div, add_zero, zero_smul, sub_zero, smul_zero]

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Geometry_LocalIntegratedCovariance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Integrated covariance correction on an open parameter domain. -/

noncomputable section
open scoped ContDiff

universe u

namespace ClosedSurfaceR4.CovarianceCorrector

variable {P E : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- The fluctuation equation uses the constant-speed hypotheses only at this parameter. -/
theorem parameterCorrector_projection_at {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} (p : P)
    (hr : average (r p) = 0) (hq : 0 < q p)
    (hcircle : ∀ t, inner ℝ (V p t) (V p t) = q p) :
    fluctuation (fun t => inner ℝ (V p t) (parameterCorrector V r q p t)) = r p :=
  corrected_projection (V p) (average (V p)) (r p).continuous hr hq.ne' hcircle _

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P] in
/-- The zero mean equation uses invertibility only at this parameter. -/
theorem parameterCorrector_average_at {V : P → C(Period, E)}
    {r : P → C(Period, ℝ)} {q : P → ℝ} (p : P) (hq : 0 < q p)
    (hcircle : ∀ t, inner ℝ (V p t) (V p t) = q p) :
    average (parameterCorrector V r q p) = 0 :=
  average_correctedVector (V p).continuous rfl (r p).continuous (q p)
    (covarianceSolution (V p) (r p) (q p))
    (covarianceSolution_equation (r p) hq hcircle)

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [CompleteSpace E] in
lemma parameterCorrector_mem_submodule_at (N : Submodule ℝ E)
    (V : P → C(Period, E)) (r : P → C(Period, ℝ)) (q : P → ℝ) (p : P)
    (hmem : ∀ t, V p t ∈ N) (hq : 0 < q p)
    (hcircle : ∀ t, inner ℝ (V p t) (V p t) = q p) (t : Period) :
    parameterCorrector V r q p t ∈ N := by
  apply N.smul_mem
  apply N.sub_mem
  · exact N.smul_mem _ (hmem t)
  · exact covarianceSolution_mem_submodule N (V p) (r p) hmem hq hcircle

end ClosedSurfaceR4.CovarianceCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LocalPeriodicCorrector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit angular corrector over its open domain of admissibility. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.PeriodicCorrector
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma contDiffOn_spanSolve {O : Set A} {Y C : A → E} {a : A → ℝ × ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O)
    (ha : ContDiffOn ℝ ∞ a O) (hD : ∀ p ∈ O, gramDet (Y p) (C p) ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => spanSolve (Y p) (C p) (a p)) O := by
  have hd : ContDiffOn ℝ ∞ (fun p => gramDet (Y p) (C p)) O :=
    ((hY.inner ℝ hY).mul (hC.inner ℝ hC)).sub ((hY.inner ℝ hC).pow 2)
  change ContDiffOn ℝ ∞ (fun p =>
    ((inner ℝ (C p) (C p) * (a p).1 - inner ℝ (Y p) (C p) * (a p).2) /
      gramDet (Y p) (C p)) • Y p +
    ((inner ℝ (Y p) (Y p) * (a p).2 - inner ℝ (Y p) (C p) * (a p).1) /
      gramDet (Y p) (C p)) • C p) O
  exact ((((hC.inner ℝ hC).mul ha.fst).sub ((hY.inner ℝ hC).mul ha.snd)).div hd hD).smul hY |>.add
    (((((hY.inner ℝ hY).mul ha.snd).sub ((hY.inner ℝ hC).mul ha.fst)).div hd hD).smul hC)

/-- A smooth family of solutions of the angular equations, with zero mean.
The varying subspace is used only for orthogonality and membership; the
actual covariance solve takes place in the fixed ambient Euclidean space. -/
theorem solve_smooth_family_on_formula (O : Set A) (hO : IsOpen O) (S : A → Submodule ℝ E) (Y C X₀ : A → E)
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX₀ : ContDiffOn ℝ ∞ X₀ O)
    (hdet : ∀ p ∈ O, gramDet (Y p) (C p) ≠ 0)
    (hPY : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (Y p) w = 0)
    (hPC : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (C p) w = 0)
    (hPX : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (X₀ p) w = 0)
    (V : A → C(Period, E)) (hVmem : ∀ p ∈ O, ∀ t, V p t ∈ S p)
    (hV : ContDiffOn ℝ ∞ (fun z : A × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (q : A → ℝ) (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (h K e : A → C(Period, ℝ))
    (hhs : ContDiffOn ℝ ∞ (fun z : A × ℝ => h z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hKs : ContDiffOn ℝ ∞ (fun z : A × ℝ => K z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hes : ContDiffOn ℝ ∞ (fun z : A × ℝ => e z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hmh : ∀ p ∈ O, average (h p) = 0) (hmK : ∀ p ∈ O, average (K p) = 0)
    (hme : ∀ p ∈ O, average (e p) = 0) :
    ∃ U D : A → C(Period, E),
      ContDiffOn ℝ ∞ (fun z : A × ℝ => U z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun z : A × ℝ => D z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      (∀ p ∈ O, average (U p) = 0) ∧
      (∀ p ∈ O, ∀ (t : ℝ), HasDerivAt (fun s : ℝ => U p (s : Period)) (D p (t : Period)) t) ∧
      (∀ p ∈ O, ∀ t, inner ℝ (C p) (U p t) = K p t ∧ inner ℝ (Y p) (D p t) = h p t) ∧
      (∀ p ∈ O, fluctuation (fun t => inner ℝ (X₀ p + V p t) (D p t)) = e p) ∧
      (∀ p ∈ O, ∀ (t : ℝ), inner ℝ (Y p) (U p (t : Period)) =
        PeriodicPrimitive.primitive (fun s : ℝ => h p (s : Period)) t) ∧
      (∀ p ∈ O, h p = 0 → K p = 0 → e p = 0 → U p = 0) ∧
      (∀ p ∈ O, ∀ t : ℝ, U p (t : Period) =
        JetPolynomial.angularCorrectionFunction (Y p) (C p) (X₀ p) (V p) (q p)
          (fun s => h p (s : Period)) (fun s => K p (s : Period))
          (fun s => e p (s : Period)) t) := by
  let H : A → C(Period, ℝ) := primitiveOn h O hO hhs hmh
  let K' : A → C(Period, ℝ) := angleOn K O hO hKs
  have hHs : ContDiffOn ℝ ∞ (fun z : A × ℝ => H z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    primitiveOn_smooth h O hO hhs hmh
  have hK's : ContDiffOn ℝ ∞ (fun z : A × ℝ => K' z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    angleOn_smooth K O hO hKs
  let T : A → C(Period, E) := fun p =>
    ⟨fun t => spanSolve (Y p) (C p) (H p t, K p t),
      (spanSolve (Y p) (C p)).continuous.comp ((H p).continuous.prodMk (K p).continuous)⟩
  let T' : A → C(Period, E) := fun p =>
    ⟨fun t => spanSolve (Y p) (C p) (h p t, K' p t),
      (spanSolve (Y p) (C p)).continuous.comp ((h p).continuous.prodMk (K' p).continuous)⟩
  have hTs : ContDiffOn ℝ ∞ (fun z : A × ℝ => T z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    contDiffOn_spanSolve (hY.comp contDiffOn_fst (fun _ hz => hz.1))
      (hC.comp contDiffOn_fst (fun _ hz => hz.1))
      (hHs.prodMk hKs) (fun z hz => hdet z.1 hz.1)
  have hT's : ContDiffOn ℝ ∞ (fun z : A × ℝ => T' z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    contDiffOn_spanSolve (hY.comp contDiffOn_fst (fun _ hz => hz.1))
      (hC.comp contDiffOn_fst (fun _ hz => hz.1))
      (hhs.prodMk hK's) (fun z hz => hdet z.1 hz.1)
  have hTd (p : A) (hp : p ∈ O) (t : ℝ) : HasDerivAt (fun s : ℝ => T p (s : Period)) (T' p (t : Period)) t :=
    (spanSolve (Y p) (C p)).hasFDerivAt.comp_hasDerivAt t
      ((primitiveOn_hasDerivAt h O hO hhs hmh hp t).prodMk (angleOn_hasDerivAt K O hO hKs hp t))
  let X : A → C(Period, E) := fun p => ContinuousMap.const Period (X₀ p) + V p
  have hXs : ContDiffOn ℝ ∞ (fun z : A × ℝ => X z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    (hX₀.comp contDiffOn_fst (fun _ hz => hz.1)).add hV
  let a : A → C(Period, ℝ) := fun p =>
    ⟨fun t => inner ℝ (X p t) (T' p t), (X p).continuous.inner (T' p).continuous⟩
  have has : ContDiffOn ℝ ∞ (fun z : A × ℝ => a z.1 (z.2 : Period)) (O ×ˢ Set.univ) := hXs.inner ℝ hT's
  let r : A → C(Period, ℝ) := fun p => e p - (a p - ContinuousMap.const Period (average (a p)))
  have hrs : ContDiffOn ℝ ∞ (fun z : A × ℝ => r z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    hes.sub (has.sub ((contDiffOn_average_joint hO has).comp contDiffOn_fst (fun _ hz => hz.1)))
  have hr0 (p : A) (hp : p ∈ O) : average (r p) = 0 := by
    change average (fun t => e p t - fluctuation (a p) t) = 0
    rw [average_sub (f := e p) (g := fluctuation (a p)) (e p).continuous
      ((a p).continuous.sub continuous_const), hme p hp, average_fluctuation (a p).continuous, sub_self]
  let W : A → C(Period, E) := correctorFamily V r q
  have hWs : ContDiffOn ℝ ∞ (fun z : A × ℝ => W z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    contDiffOn_parameterCorrector_joint hO hV hrs hq hqpos hcircle
  have hW0 (p : A) (hp : p ∈ O) : average (W p) = 0 := parameterCorrector_average_at p (hqpos p hp) (hcircle p hp)
  let Z : A → C(Period, E) := primitiveOn W O hO hWs hW0
  have hZs : ContDiffOn ℝ ∞ (fun z : A × ℝ => Z z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    primitiveOn_smooth W O hO hWs hW0
  have hWmem (p : A) (hp : p ∈ O) (t : Period) : W p t ∈ S p :=
    parameterCorrector_mem_submodule_at (S p) V r q p (hVmem p hp) (hqpos p hp) (hcircle p hp) t
  have hZmem (p : A) (hp : p ∈ O) (t : Period) : Z p t ∈ S p := by
    refine Quotient.inductionOn' t ?_
    intro x
    rw [primitiveOn_apply W O hO hWs hW0 hp]
    exact PeriodicPrimitive.primitive_mem_submodule (S p)
      ((W p).continuous.comp (AddCircle.continuous_mk' 1)) (fun s => hWmem p hp (s : Period)) x
  let U : A → C(Period, E) := fun p => T p + Z p
  let D : A → C(Period, E) := fun p => T' p + W p
  have hU0 (p : A) (hp : p ∈ O) : average (U p) = 0 := by
    change average (fun t => T p t + Z p t) = 0
    rw [average_add (f := T p) (g := Z p) (T p).continuous (Z p).continuous]
    have ht0 := average_spanSolve (Y p) (C p) (H p).continuous (K p).continuous
      (primitiveOn_mean_zero h O hO hhs hmh hp) (hmK p hp)
    change average (T p) = 0 at ht0
    rw [ht0, zero_add]
    exact primitiveOn_mean_zero W O hO hWs hW0 hp
  refine ⟨U, D, hTs.add hZs, hT's.add hWs, hU0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp t
    exact (hTd p hp t).add (primitiveOn_hasDerivAt W O hO hWs hW0 hp t)
  · intro p hp t
    have hy := hPY p hp (W p t) (hWmem p hp t)
    have hc := hPC p hp (Z p t) (hZmem p hp t)
    change inner ℝ (C p) (T p t + Z p t) = _ ∧ inner ℝ (Y p) (T' p t + W p t) = _
    rw [inner_add_right, hc, add_zero, inner_add_right, hy, add_zero]
    exact ⟨(spanSolve_pairings (Y p) (C p) (hdet p hp) _).2,
      (spanSolve_pairings (Y p) (C p) (hdet p hp) _).1⟩
  · intro p hp
    have hs := parameterCorrector_projection_at p (hr0 p hp) (hqpos p hp) (hcircle p hp)
    have heq : (fun t => inner ℝ (X₀ p + V p t) (D p t)) =
        (fun t => a p t + inner ℝ (V p t) (W p t)) := by
      funext t
      change inner ℝ (X₀ p + V p t) (T' p t + W p t) =
        inner ℝ (X₀ p + V p t) (T' p t) + inner ℝ (V p t) (W p t)
      simp only [inner_add_right, inner_add_left, hPX p hp _ (hWmem p hp t), zero_add]
    rw [heq]
    change (fun t => a p t + inner ℝ (V p t) (W p t) -
      average (fun s => a p s + inner ℝ (V p s) (W p s))) = e p
    rw [average_add (a p).continuous ((V p).continuous.inner (W p).continuous)]
    funext t
    have ht := congrFun hs t
    change inner ℝ (V p t) (W p t) - average (fun s => inner ℝ (V p s) (W p s)) =
      e p t - (a p t - average (a p)) at ht
    linarith
  · intro p hp t
    change inner ℝ (Y p) (T p (t : Period) + Z p (t : Period)) = _
    rw [inner_add_right, hPY p hp _ (hZmem p hp (t : Period)), add_zero]
    exact (spanSolve_pairings (Y p) (C p) (hdet p hp) (H p (t : Period), K p (t : Period))).1.trans
      (primitiveOn_apply h O hO hhs hmh hp t)
  · intro p hp hh hK he
    have hHp : H p = 0 := primitiveOn_zero_at h O hO hhs hmh hp hh
    have hK'p : K' p = 0 := angleOn_zero_at K O hO hKs hp hK
    have hTp : T p = 0 := by
      ext t
      change spanSolve (Y p) (C p) (H p t, K p t) = 0
      rw [hHp, hK]
      exact (spanSolve (Y p) (C p)).map_zero
    have hT'p : T' p = 0 := by
      ext t
      change spanSolve (Y p) (C p) (h p t, K' p t) = 0
      rw [hh, hK'p]
      exact (spanSolve (Y p) (C p)).map_zero
    have hap : a p = 0 := by
      ext t
      change inner ℝ (X p t) (T' p t) = 0
      rw [hT'p]
      exact inner_zero_right _
    have hrp : r p = 0 := by
      ext t
      change e p t - (a p t - average (a p)) = 0
      rw [he, hap]
      change (0 : ℝ) - (0 - average (fun _ => (0 : ℝ))) = 0
      rw [average_const, sub_self, sub_self]
    have hWp : W p = 0 := by
      ext t
      exact parameterCorrector_zero (fun s => congrArg (fun f : C(Period, ℝ) => f s) hrp) t
    have hZp : Z p = 0 := primitiveOn_zero_at W O hO hWs hW0 hp hWp
    change T p + Z p = 0
    rw [hTp, hZp, add_zero]

  · intro p hp t
    have hk (s : ℝ) : K' p (s : Period) = deriv (fun u : ℝ => K p (u : Period)) s :=
      (angleOn_hasDerivAt K O hO hKs hp s).deriv.symm
    have hr (s : ℝ) : r p (s : Period) =
        JetPolynomial.angularSourceFunction (Y p) (C p) (X₀ p) (V p)
          (fun u => h p (u : Period)) (fun u => K p (u : Period))
          (fun u => e p (u : Period)) s := by
      have havg : average (a p) = ∫ u in 0..1, a p (u : Period) :=
        (PeriodicPrimitive.integral_lift_eq_haar (a p)).symm
      change e p (s : Period) - (a p (s : Period) - average (a p)) = _
      rw [havg]
      change e p (s : Period) -
        (inner ℝ (X₀ p + V p (s : Period))
          (spanSolve (Y p) (C p) (h p (s : Period), K' p (s : Period))) -
          ∫ u in 0..1, inner ℝ (X₀ p + V p (u : Period))
            (spanSolve (Y p) (C p) (h p (u : Period), K' p (u : Period)))) = _
      simp only [JetPolynomial.angularSourceFunction, hk]
    change T p (t : Period) + Z p (t : Period) = _
    rw [primitiveOn_apply W O hO hWs hW0 hp]
    change spanSolve (Y p) (C p) (H p (t : Period), K p (t : Period)) + _ = _
    rw [primitiveOn_apply h O hO hhs hmh hp]
    unfold JetPolynomial.angularCorrectionFunction
    congr 1
    congr 1
    funext s
    change parameterCorrector V r q p (s : Period) = _
    rw [← realCorrector_eq_parameterCorrector V q r p s]
    congr 1
    exact funext hr

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialFullCorrector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial construction for every component of the complete periodic
corrector. Only the transverse derivative increases the highest jet order. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace Expression

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smoothCoeffs_spanTerm {O : Set LowJet} {Y C : LowJet → E}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O)
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0) (L : E →L[ℝ] ℝ)
    {H K : Expression} (hH : H.SmoothCoeffs O) (hK : K.SmoothCoeffs O) :
    (spanTerm Y C L H K).SmoothCoeffs O := by
  have hb (b : ℝ × ℝ) : ContDiffOn ℝ ∞ (spanCoefficient Y C L b) (O ×ˢ Set.univ) :=
    (L.contDiff.comp_contDiffOn (contDiffOn_spanSolve hY hC contDiffOn_const hd)).comp
      contDiffOn_fst (fun _ hz => hz.1)
  exact ⟨smoothCoeffs_mul (hb (1, 0)) hH, smoothCoeffs_mul (hb (0, 1)) hK⟩

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma smoothCoeffs_angularSource {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → E} {V : LowJet → C(Period, E)}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O)
    (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0)
    {h K e : Expression} (hh : h.SmoothCoeffs O) (hK : K.SmoothCoeffs O)
    (he : e.SmoothCoeffs O) : (angularSource Y C X₀ V h K e).SmoothCoeffs O := by
  have hb (b : ℝ × ℝ) : ContDiffOn ℝ ∞ (metricCoefficient Y C X₀ V b) (O ×ˢ Set.univ) :=
    ((hX.comp contDiffOn_fst (fun _ hz => hz.1)).add hV).inner ℝ
      ((contDiffOn_spanSolve hY hC contDiffOn_const hd).comp contDiffOn_fst (fun _ hz => hz.1))
  exact smoothCoeffs_sub he (smoothCoeffs_fluct hO
    ⟨smoothCoeffs_mul (hb (1, 0)) hh, smoothCoeffs_mul (hb (0, 1)) (smoothCoeffs_angle hO hK)⟩)

lemma smoothCoeffs_fullComponent {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → E} {V : LowJet → C(Period, E)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (L : E →L[ℝ] ℝ) (v : Fin 2) {h j e : Expression}
    (hh : h.SmoothCoeffs O) (hj : j.SmoothCoeffs O) (he : e.SmoothCoeffs O) :
    (fullComponent Y C X₀ V q L v h j e).SmoothCoeffs O := by
  have hH := smoothCoeffs_primitive hO hh
  have hK := smoothCoeffs_sub (smoothCoeffs_slow hO v hH) hj
  exact ⟨smoothCoeffs_spanTerm hY hC hd L hH hK,
    smoothCoeffs_primitive hO (smoothCoeffs_covariance hO hV hq hqp hcircle L
      (smoothCoeffs_angularSource hO hY hC hX hV hd hh hK he))⟩

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialEvaluation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Evaluation identities connecting the finite jet expressions to the
explicit span and covariance formulas of the periodic corrector. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma spanSolve_decompose (Y C : E) (a b : ℝ) :
    spanSolve Y C (a, b) = a • spanSolve Y C (1, 0) + b • spanSolve Y C (0, 1) := by
  have hp : (a, b) = a • ((1, 0) : ℝ × ℝ) + b • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  conv_lhs => rw [hp, map_add, map_smul, map_smul]

namespace Expression

lemma eval_spanTerm (Y C : LowJet → E) (L : E →L[ℝ] ℝ) (H K : Expression)
    (G : Base → Space) (p : Base) (t : ℝ) :
    (spanTerm Y C L H K).eval G (p, t) =
      L (spanSolve (Y (lowJet G p)) (C (lowJet G p)) (H.eval G (p, t), K.eval G (p, t))) := by
  conv_rhs => rw [spanSolve_decompose]
  simp only [spanTerm, eval, eval_mul, spanCoefficient,
    map_add, map_smul, smul_eq_mul]
  ring

lemma eval_metricTerm (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (h K : Expression) (G : Base → Space) (p : Base) (t : ℝ) :
    (Expression.add ((Expression.coeff (metricCoefficient Y C X₀ V (1, 0))).mul h)
      ((Expression.coeff (metricCoefficient Y C X₀ V (0, 1))).mul K)).eval G (p, t) =
    inner ℝ (X₀ (lowJet G p) + V (lowJet G p) (t : Period))
      (spanSolve (Y (lowJet G p)) (C (lowJet G p)) (h.eval G (p, t), K.eval G (p, t))) := by
  conv_rhs => rw [spanSolve_decompose]
  simp only [eval, eval_mul, metricCoefficient,
    inner_add_right, inner_smul_right]
  ring

lemma eval_angularSource {O : Set LowJet} (hO : IsOpen O)
    (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    {h K e : Expression} (hh : h.SmoothCoeffs O) (hK : K.SmoothCoeffs O)
    (hb : ∀ b : ℝ × ℝ, ContDiffOn ℝ ∞ (metricCoefficient Y C X₀ V b) (O ×ˢ Set.univ))
    (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    (angularSource Y C X₀ V h K e).eval G (p, t) =
      let a := fun s : ℝ => inner ℝ (X₀ (lowJet G p) + V (lowJet G p) (s : Period))
        (spanSolve (Y (lowJet G p)) (C (lowJet G p))
          (h.eval G (p, s), deriv (fun u => K.eval G (p, u)) s))
      e.eval G (p, t) - (a t - ∫ s in 0..1, a s) := by
  let f : Expression := Expression.add ((Expression.coeff (metricCoefficient Y C X₀ V (1, 0))).mul h)
    ((Expression.coeff (metricCoefficient Y C X₀ V (0, 1))).mul K.angle)
  have hf : f.SmoothCoeffs O :=
    ⟨smoothCoeffs_mul (hb (1, 0)) hh, smoothCoeffs_mul (hb (0, 1)) (smoothCoeffs_angle hO hK)⟩
  have ha (s : ℝ) : f.eval G (p, s) =
      inner ℝ (X₀ (lowJet G p) + V (lowJet G p) (s : Period))
        (spanSolve (Y (lowJet G p)) (C (lowJet G p))
          (h.eval G (p, s), deriv (fun u => K.eval G (p, u)) s)) := by
    rw [show f = Expression.add ((Expression.coeff (metricCoefficient Y C X₀ V (1, 0))).mul h)
      ((Expression.coeff (metricCoefficient Y C X₀ V (0, 1))).mul K.angle) from rfl,
      eval_metricTerm, eval_angle hO hK G hp]
  change (e.sub f.fluct).eval G (p, t) = _
  rw [eval_sub]
  rw [eval_fluct hO hf G hp, ha]
  simp only [ha]

lemma eval_transverseDatum {O : Set LowJet} {S : Set Base} (hO : IsOpen O) (hS : IsOpen S)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (v : Fin 2) {h j : Expression} (hh : h.SmoothCoeffs O) {p : Base} (hp : p ∈ S) (t : ℝ) :
    ((h.primitive.slow v).sub j).eval G (p, t) =
      fderiv ℝ (fun x => PeriodicPrimitive.primitive (fun s => h.eval G (x, s)) t)
        p (coordinateVector v) - j.eval G (p, t) := by
  rw [eval_sub, eval_slow hO hS hG hQ v (smoothCoeffs_primitive hO hh) hp]
  have heq : (fun x => h.primitive.eval G (x, t)) =ᶠ[nhds p]
      (fun x => PeriodicPrimitive.primitive (fun s => h.eval G (x, s)) t) := by
    filter_upwards [hS.mem_nhds hp] with x hx
    exact eval_primitive hO hh G (hQ hx) t
  rw [heq.fderiv_eq]

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_LocalFullPeriodicCorrector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.ofLocal_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.vectorMean_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.zero_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete periodic corrector with all hypotheses restricted to an open chart domain. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.PeriodicCorrector
open CovarianceCorrector LocalPeriodicCalculus
open SmoothPeriodicCalculus (slowDerivative)

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma directional_pairing_constraint_on {O : Set A} (hO : IsOpen O) {Y U : A → E}
    {H : A → ℝ} {p v : A} (hp : p ∈ O) {C : E} {j : ℝ}
    (hY : DifferentiableAt ℝ Y p) (hU : DifferentiableAt ℝ U p)
    (hH : DifferentiableAt ℝ H p) (he : ∀ q ∈ O, inner ℝ (Y q) (U q) = H q)
    (hC : fderiv ℝ Y p v = C)
    (hK : inner ℝ C (U p) = fderiv ℝ H p v - j) :
    inner ℝ (Y p) (fderiv ℝ U p v) = j := by
  have hd := hY.hasFDerivAt.inner ℝ hU.hasFDerivAt
  have hid : (fun q => inner ℝ (Y q) (U q)) =ᶠ[𝓝 p] H := by
    filter_upwards [hO.mem_nhds hp] with q hq
    exact he q hq
  have hv := congrArg (fun L : A →L[ℝ] ℝ => L v)
    ((hd.congr_of_eventuallyEq hid.symm).unique hH.hasFDerivAt)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    fderivInnerCLM_apply] at hv
  rw [hC] at hv
  linarith

/-- A mean-zero, jointly smooth solution of the complete periodic system.
The transverse equation follows from differentiating the pairing with `Y`. -/
theorem solve_full_smooth_family_on_formula (O : Set A) (hO : IsOpen O) (v : A) (S : A → Submodule ℝ E) (Y C X₀ : A → E)
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX₀ : ContDiffOn ℝ ∞ X₀ O)
    (hYC : ∀ p ∈ O, fderiv ℝ Y p v = C p)
    (hdet : ∀ p ∈ O, gramDet (Y p) (C p) ≠ 0)
    (hPY : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (Y p) w = 0)
    (hPC : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (C p) w = 0)
    (hPX : ∀ p ∈ O, ∀ w, w ∈ S p → inner ℝ (X₀ p) w = 0)
    (V : A → C(Period, E)) (hVmem : ∀ p ∈ O, ∀ t, V p t ∈ S p)
    (hV : ContDiffOn ℝ ∞ (fun z : A × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (q : A → ℝ) (hq : ContDiffOn ℝ ∞ q O) (hqpos : ∀ p ∈ O, 0 < q p)
    (hcircle : ∀ p ∈ O, ∀ t, inner ℝ (V p t) (V p t) = q p)
    (h j e : A → C(Period, ℝ))
    (hhs : ContDiffOn ℝ ∞ (fun z : A × ℝ => h z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hjs : ContDiffOn ℝ ∞ (fun z : A × ℝ => j z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hes : ContDiffOn ℝ ∞ (fun z : A × ℝ => e z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hmh : ∀ p ∈ O, average (h p) = 0) (hmj : ∀ p ∈ O, average (j p) = 0)
    (hme : ∀ p ∈ O, average (e p) = 0) :
    ∃ U D : A → C(Period, E),
      ContDiffOn ℝ ∞ (fun z : A × ℝ => U z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      ContDiffOn ℝ ∞ (fun z : A × ℝ => D z.1 (z.2 : Period)) (O ×ˢ Set.univ) ∧
      (∀ p ∈ O, average (U p) = 0) ∧
      (∀ p ∈ O, ∀ (t : ℝ), HasDerivAt (fun s : ℝ => U p (s : Period))
        (D p (t : Period)) t) ∧
      (∀ p ∈ O, ∀ t, inner ℝ (Y p) (D p t) = h p t) ∧
      (∀ p ∈ O, ∀ (t : ℝ), inner ℝ (Y p)
        (slowDerivative (fun z : A × ℝ => U z.1 (z.2 : Period)) v (p, t)) = j p (t : Period)) ∧
      (∀ p ∈ O, fluctuation (fun t => inner ℝ (X₀ p + V p t) (D p t)) = e p) ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, h p = 0) →
        (∀ p ∈ Z, j p = 0) → (∀ p ∈ Z, e p = 0) → ∀ p ∈ Z, U p = 0) ∧
      (∀ p ∈ O, ∀ t : ℝ, U p (t : Period) = fullSolutionFormula v Y C X₀ V q h j e (p, t)) := by
  let H := primitiveOn h O hO hhs hmh
  have hHs : ContDiffOn ℝ ∞ (fun z : A × ℝ => H z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    primitiveOn_smooth h O hO hhs hmh
  have hH0 : ∀ p ∈ O, average (H p) = 0 := fun p hp => primitiveOn_mean_zero h O hO hhs hmh hp
  let Hᵥ := slowOn H O hO hHs v
  have hHᵥs : ContDiffOn ℝ ∞ (fun z : A × ℝ => Hᵥ z.1 (z.2 : Period)) (O ×ˢ Set.univ) :=
    slowOn_smooth H O hO hHs v
  let K : A → C(Period, ℝ) := fun p => Hᵥ p - j p
  have hKs : ContDiffOn ℝ ∞ (fun z : A × ℝ => K z.1 (z.2 : Period)) (O ×ˢ Set.univ) := hHᵥs.sub hjs
  have hK0 (p : A) (hp : p ∈ O) : average (K p) = 0 := by
    have hv0 : average (Hᵥ p) = 0 := slowOn_mean_zero H O hO hHs hH0 v hp
    change average (fun t => Hᵥ p t - j p t) = 0
    rw [average_sub (f := Hᵥ p) (g := j p) (Hᵥ p).continuous (j p).continuous,
      hv0, hmj p hp, sub_self]
  obtain ⟨U, D, hUs, hDs, hU0, hUd, hpair, hfluc, hUH, hzero, hformula⟩ :=
    solve_smooth_family_on_formula O hO S Y C X₀ hY hC hX₀ hdet hPY hPC hPX V hVmem hV
      q hq hqpos hcircle h K e hhs hKs hes hmh hK0 hme
  refine ⟨U, D, hUs, hDs, hU0, hUd, fun p hp t => (hpair p hp t).2, ?_, hfluc, ?_, ?_⟩
  · intro p hp t
    have hUt : ContDiffAt ℝ ∞ (fun q => U q (t : Period)) p :=
      (hUs.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt
    have hHt : ContDiffAt ℝ ∞ (fun q => H q (t : Period)) p :=
      (hHs.contDiffAt ((hO.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
        (contDiff_id.prodMk contDiff_const).contDiffAt
    have he : ∀ q ∈ O, inner ℝ (Y q) (U q (t : Period)) = H q (t : Period) := by
      intro q hq
      exact (hUH q hq t).trans (primitiveOn_apply h O hO hhs hmh hq t).symm
    have hK : inner ℝ (C p) (U p (t : Period)) =
        fderiv ℝ (fun q => H q (t : Period)) p v - j p (t : Period) := by
      rw [LocalPeriodicCalculus.fderiv_slice hO hHs hp]
      have hk := (hpair p hp (t : Period)).1
      change inner ℝ (C p) (U p (t : Period)) = Hᵥ p (t : Period) - j p (t : Period) at hk
      rw [slowOn_apply H O hO hHs v hp] at hk
      exact hk
    have hd := directional_pairing_constraint_on hO hp
      ((hY.contDiffAt (hO.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
      (hUt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (hHt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) he (hYC p hp) hK
    rwa [LocalPeriodicCalculus.fderiv_slice hO hUs hp] at hd
  · intro Z hZ hZO hhZ hjZ heZ p hp
    have hHZ : ∀ q ∈ Z, H q = 0 :=
      fun q hq => primitiveOn_zero_at h O hO hhs hmh (hZO hq) (hhZ q hq)
    have hHvp : Hᵥ p = 0 := slowOn_zero_on H O hO hHs hZ hHZ v (hZO hp) hp
    have hKp : K p = 0 := by
      change Hᵥ p - j p = 0
      rw [hHvp, hjZ p hp, sub_self]
    exact hzero p (hZO hp) (hhZ p hp) hKp (heZ p hp)

  · intro p hp t
    have hK : (fun s : ℝ => K p (s : Period)) = fun s : ℝ =>
        fderiv ℝ (fun q => PeriodicPrimitive.primitive (fun u : ℝ => h q (u : Period)) s)
          p v - j p (s : Period) := by
      funext s
      change Hᵥ p (s : Period) - j p (s : Period) = _
      rw [slowOn_apply H O hO hHs v hp, ← fderiv_slice hO hHs hp]
      have heq : (fun q => H q (s : Period)) =ᶠ[𝓝 p]
          (fun q => PeriodicPrimitive.primitive (fun u : ℝ => h q (u : Period)) s) := by
        filter_upwards [hO.mem_nhds hp] with q hq
        exact primitiveOn_apply h O hO hhs hmh hq s
      rw [heq.fderiv_eq]
    rw [hformula p hp t, hK]
    rfl

end ClosedSurfaceR4.PeriodicCorrector

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_ExplicitPeriodicFormula
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial expression evaluates to the explicit vector-valued
periodic correction, including its covariance inverse and normalized integral. -/
noncomputable section
open MeasureTheory
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma realCorrector_continuous (V : C(Period, E)) (q : ℝ) {f : ℝ → ℝ}
    (hf : Continuous f) : Continuous (realCorrector V q f) := by
  have hv : Continuous (fun t : ℝ => V (t : Period)) :=
    V.continuous.comp (AddCircle.continuous_mk' 1)
  exact continuous_const.smul ((hf.add (((hv.sub continuous_const).inner continuous_const).div_const q)).smul hv
    |>.sub continuous_const)

variable [CompleteSpace E]

lemma primitive_map (L : E →L[ℝ] ℝ) {f : ℝ → E} (hf : Continuous f) (t : ℝ) :
    L (PeriodicPrimitive.primitive f t) = PeriodicPrimitive.primitive (fun s => L (f s)) t := by
  have hr (s : ℝ) : L (PeriodicPrimitive.rawPrimitive f s) =
      PeriodicPrimitive.rawPrimitive (fun u => L (f u)) s :=
    (L.intervalIntegral_comp_comm (hf.intervalIntegrable 0 s)).symm
  simp only [PeriodicPrimitive.primitive, map_sub, hr]
  rw [← L.intervalIntegral_comp_comm
    ((PeriodicPrimitive.rawPrimitive_continuous hf).intervalIntegrable 0 1)]
  simp only [hr]

variable [FiniteDimensional ℝ E]

namespace Expression

/-- The symbolic construction is exactly the span-plus-integrated-covariance
formula, not just a formal expression with a similar order bound. -/
theorem eval_angularCorrection {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → E} {V : LowJet → C(Period, E)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (L : E →L[ℝ] ℝ) {h K e : Expression}
    (hh : h.SmoothCoeffs O) (hK : K.SmoothCoeffs O) (he : e.SmoothCoeffs O)
    (G : Base → Space) {p : Base} (hp : lowJet G p ∈ O) (t : ℝ) :
    (Expression.add (spanTerm Y C L h.primitive K)
      ((angularSource Y C X₀ V h K e).covariance V q L).primitive).eval G (p, t) =
    L (angularCorrectionFunction (Y (lowJet G p)) (C (lowJet G p)) (X₀ (lowJet G p))
      (V (lowJet G p)) (q (lowJet G p))
      (fun s => h.eval G (p, s)) (fun s => K.eval G (p, s)) (fun s => e.eval G (p, s)) t) := by
  let r := angularSource Y C X₀ V h K e
  have hr : r.SmoothCoeffs O := smoothCoeffs_angularSource hO hY hC hX hV hd hh hK he
  have hw := smoothCoeffs_covariance hO hV hq hqp hcircle L hr
  have hb (b : ℝ × ℝ) : ContDiffOn ℝ ∞ (metricCoefficient Y C X₀ V b) (O ×ˢ Set.univ) :=
    ((hX.comp contDiffOn_fst (fun _ hz => hz.1)).add hV).inner ℝ
      ((contDiffOn_spanSolve hY hC contDiffOn_const hd).comp contDiffOn_fst (fun _ hz => hz.1))
  have hs (s : ℝ) : r.eval G (p, s) =
      angularSourceFunction (Y (lowJet G p)) (C (lowJet G p)) (X₀ (lowJet G p))
        (V (lowJet G p)) (fun u => h.eval G (p, u)) (fun u => K.eval G (p, u))
        (fun u => e.eval G (p, u)) s :=
    eval_angularSource hO Y C X₀ V hh hK hb G hp s
  have hf : Continuous (fun s => r.eval G (p, s)) := (eval_slice_smooth hO hr G hp).continuous
  have hW := realCorrector_continuous (V (lowJet G p)) (q (lowJet G p)) hf
  change (spanTerm Y C L h.primitive K).eval G (p, t) +
    (r.covariance V q L).primitive.eval G (p, t) = _
  rw [eval_spanTerm, eval_primitive hO hh G hp, eval_primitive hO hw G hp]
  simp only [angularCorrectionFunction, map_add]
  have heq : (fun s => r.eval G (p, s)) =
      angularSourceFunction (Y (lowJet G p)) (C (lowJet G p)) (X₀ (lowJet G p))
        (V (lowJet G p)) (fun u => h.eval G (p, u)) (fun u => K.eval G (p, u))
        (fun u => e.eval G (p, u)) := funext hs
  rw [← heq, primitive_map L hW]
  congr 1
  congr 1
  funext s
  exact eval_covariance hO V q L hr G hp s

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialFullEvaluation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Identification of the complete polynomial expression with the same
explicit solution supplied by the full periodic system theorem. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial.Expression
open CovarianceCorrector PeriodicCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Polynomial forcing produces the explicit full corrector. The derivative
in the transverse datum is the actual derivative of the forcing primitive. -/
theorem eval_fullComponent {O : Set LowJet} {S : Set Base} (hO : IsOpen O) (hS : IsOpen S)
    {Y C X₀ : LowJet → E} {V : LowJet → C(Period, E)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (L : E →L[ℝ] ℝ) (v : Fin 2) {h j e : Expression}
    (hh : h.SmoothCoeffs O) (hj : j.SmoothCoeffs O) (he : e.SmoothCoeffs O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (hf jf ef : Base → C(Period, ℝ))
    (hhr : ∀ p ∈ S, ∀ t : ℝ, h.eval G (p, t) = hf p (t : Period))
    (hjr : ∀ p ∈ S, ∀ t : ℝ, j.eval G (p, t) = jf p (t : Period))
    (her : ∀ p ∈ S, ∀ t : ℝ, e.eval G (p, t) = ef p (t : Period))
    {p : Base} (hp : p ∈ S) (t : ℝ) :
    (fullComponent Y C X₀ V q L v h j e).eval G (p, t) =
      L (fullSolutionFormula (coordinateVector v) (fun x => Y (lowJet G x))
        (fun x => C (lowJet G x)) (fun x => X₀ (lowJet G x))
        (fun x => V (lowJet G x)) (fun x => q (lowJet G x)) hf jf ef (p, t)) := by
  let K := (h.primitive.slow v).sub j
  have hK : K.SmoothCoeffs O :=
    smoothCoeffs_sub (smoothCoeffs_slow hO v (smoothCoeffs_primitive hO hh)) hj
  have hk : (fun s => K.eval G (p, s)) = fun s : ℝ =>
      fderiv ℝ (fun x => PeriodicPrimitive.primitive (fun u : ℝ => hf x (u : Period)) s)
        p (coordinateVector v) - jf p (s : Period) := by
    funext s
    rw [show K = (h.primitive.slow v).sub j from rfl,
      eval_transverseDatum hO hS hG hQ v hh hp, hjr p hp s]
    have heq : (fun x => PeriodicPrimitive.primitive (fun u => h.eval G (x, u)) s) =ᶠ[𝓝 p]
        (fun x => PeriodicPrimitive.primitive (fun u : ℝ => hf x (u : Period)) s) := by
      filter_upwards [hS.mem_nhds hp] with x hx
      rw [show (fun u => h.eval G (x, u)) = (fun u : ℝ => hf x (u : Period)) from
        funext (hhr x hx)]
    rw [heq.fderiv_eq]
  have hhp : (fun s => h.eval G (p, s)) = (fun s : ℝ => hf p (s : Period)) :=
    funext (hhr p hp)
  have hep : (fun s => e.eval G (p, s)) = (fun s : ℝ => ef p (s : Period)) :=
    funext (her p hp)
  change (Expression.add (spanTerm Y C L h.primitive K)
    ((angularSource Y C X₀ V h K e).covariance V q L).primitive).eval G (p, t) = _
  rw [eval_angularCorrection hO hY hC hX hV hd hq hqp hcircle L hh hK he G (hQ hp),
    hhp, hep, hk]
  rfl

end ClosedSurfaceR4.JetPolynomial.Expression

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

lemma angle_hasDerivAt (F : Family O E) {p : A} (hp : p ∈ O) (t : ℝ) :
    HasDerivAt (fun s : ℝ => F.val p (s : Period)) (F.angle.val p (t : Period)) t := by
  rw [angle, ofLocal_apply _ _ hp]
  exact angleOn_hasDerivAt F.val O O.isOpen F.smooth hp t

@[simp] lemma slow_apply (F : Family O E) (v : A) {p : A} (hp : p ∈ O) (t : ℝ) :
    (F.slow v).val p (t : Period) =
      SmoothPeriodicCalculus.slowDerivative (fun z : A × ℝ => F.val z.1 (z.2 : Period)) v (p, t) := by
  rw [slow, ofLocal_apply _ _ hp, slowOn_apply _ _ _ _ _ hp]

variable [FiniteDimensional ℝ A] [CompleteSpace E]

lemma primitive_mean_zero (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0)
    {p : A} (hp : p ∈ O) : average ((F.primitive hm).val p) = 0 := by
  have he : (F.primitive hm).val p = primitiveOn F.val O O.isOpen F.smooth hm p := by
    ext t
    exact ofLocal_apply _ _ hp t
  rw [he]
  exact primitiveOn_mean_zero _ _ _ _ _ hp

end Family
end ClosedSurfaceR4.LocalPeriodicExpansion

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

lemma inner_add_right (F G H : Family O E) : F.inner (G + H) = F.inner G + F.inner H := by
  ext p hp t
  simp only [inner_apply, add_apply, _root_.inner_add_right]

lemma angle_zero_at (F : Family O E) {p : A} (hp : p ∈ O) (hz : F.val p = 0) :
    F.angle.val p = 0 := by
  ext t
  refine Quotient.inductionOn' t ?_
  intro x
  have hd := F.angle_hasDerivAt hp x
  rw [hz] at hd
  exact hd.unique (hasDerivAt_const x 0)

lemma slow_zero_on (F : Family O E) {Z : Set A} (hZ : IsOpen Z)
    (hz : ∀ p ∈ Z, F.val p = 0) (v : A) {p : A} (hp : p ∈ O) (hpZ : p ∈ Z) :
    (F.slow v).val p = 0 := by
  have he : (F.slow v).val p = slowOn F.val O O.isOpen F.smooth v p := by
    ext t
    exact ofLocal_apply _ _ hp _
  rw [he]
  exact slowOn_zero_on _ _ _ _ hZ hz v hp hpZ

variable [FiniteDimensional ℝ A] [CompleteSpace E]

lemma primitive_mem (F : Family O E) (hm : ∀ p ∈ O, average (F.val p) = 0)
    [FiniteDimensional ℝ E] (S : A → Submodule ℝ E)
    (hS : ∀ p ∈ O, ∀ t, F.val p t ∈ S p) {p : A} (hp : p ∈ O) (t : Period) :
    (F.primitive hm).val p t ∈ S p := by
  rw [primitive, ofLocal_apply _ _ hp]
  refine Quotient.inductionOn' t ?_
  intro x
  rw [primitiveOn_apply _ _ _ _ _ hp]
  exact PeriodicPrimitive.primitive_mem_submodule (S p)
    ((F.val p).continuous.comp (AddCircle.continuous_mk' 1)) (fun s => hS p hp (s : Period)) x

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

namespace ClosedSurfaceR4.LocalPeriodicExpansion.Family
open CovarianceCorrector
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] {O : TopologicalSpace.Opens A}

lemma fluct_mean_zero (F : Family O ℝ) (p : A) : average (F.fluct.val p) = 0 := by
  change average (fun t => F.fluct.val p t) = 0
  simp only [fluct_apply]
  exact PeriodicCorrector.average_fluctuation (F.val p).continuous

lemma mean_add (F G : Family O ℝ) : (F + G).mean = F.mean + G.mean := by
  ext p hp t
  simp only [mean_apply, add_apply]
  exact average_add (F.val p).continuous (G.val p).continuous
lemma mean_smul (c : ℝ) (F : Family O ℝ) : (c • F).mean = c • F.mean := by
  ext p hp t
  simp only [mean_apply, smul_apply]
  exact average_const_smul c (F.val p)
lemma fluct_add (F G : Family O ℝ) : (F + G).fluct = F.fluct + G.fluct := by
  simp only [fluct, mean_add]
  abel
lemma fluct_smul (c : ℝ) (F : Family O ℝ) : (c • F).fluct = c • F.fluct := by
  simp only [fluct, mean_smul, smul_sub]
lemma fluct_fluct (F : Family O ℝ) : F.fluct.fluct = F.fluct := by
  have hm : F.fluct.mean = 0 := by
    ext p hp t
    simpa only [mean_apply, zero_apply] using F.fluct_mean_zero p
  rw [fluct, hm, sub_zero]
lemma fluct_zero_at (F : Family O ℝ) {p : A} (hz : F.val p = 0) : F.fluct.val p = 0 := by
  ext t
  simp only [fluct_apply, fluctuation, hz]
  change (0 : ℝ) - average (fun _ => (0 : ℝ)) = 0
  rw [average_const, sub_self]

end ClosedSurfaceR4.LocalPeriodicExpansion.Family

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVector
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instMetricSpaceOneJet _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.circularPhaseBoundaryCurve_carrier _root_.OAI.ClosedSurfaceR4.FiniteOrderSmoothing.directionJetLinearization_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_scale _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_C _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_J _root_.OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.atUnperturbedScale_e _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_apply _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowJetPosition_variationLowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.lowPosition_lowJet _root_.OAI.ClosedSurfaceR4.JetPolynomial.spatialAmplitude_lowJet _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_apply _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_one _root_.OAI.ClosedSurfaceR4.SurfaceJetCoordinates.baseEquiv_zero _root_.OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.withSpatialAmplitude_amplitude _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Four coordinate polynomials represent the actual vector families used by
the metric recursion. Dot products and both derivatives preserve representation. -/
noncomputable section
open scoped ContDiff Topology BigOperators

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion SmoothPeriodicCalculus

namespace VectorExpression

lemma smoothCoeffs_dot {O : Set LowJet} {R T : VectorExpression}
    (hR : R.SmoothCoeffs O) (hT : T.SmoothCoeffs O) : (R.dot T).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumList
  intro i _
  exact Expression.smoothCoeffs_mul (hR i) (hT i)

lemma represents_add {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) : Represents G (R.add T) (U + W) := by
  intro i p hp t
  simp only [add, Expression.eval, hR i p hp t, hT i p hp t, Family.add_apply]
  rfl

lemma eval_dot {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) {p : Base} (hp : p ∈ S) (t : ℝ) :
    (R.dot T).eval G (p, t) = inner ℝ (U.val p (t : CovarianceCorrector.Period))
      (W.val p (t : CovarianceCorrector.Period)) := by
  rw [dot, Expression.eval_sumList, ← List.sum_toFinset _ Finset.univ.nodup_toList,
    Finset.toList_toFinset]
  simp only [Expression.eval_mul, hR _ p hp t, hT _ p hp t]
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i : Fin 4, U.val p (t : CovarianceCorrector.Period) i *
    W.val p (t : CovarianceCorrector.Period) i) =
    ∑ i : Fin 4, W.val p (t : CovarianceCorrector.Period) i * U.val p (t : CovarianceCorrector.Period) i
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

lemma represents_slow {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) (v : Fin 2) : Represents G (R.slow v) (U.slow (coordinateVector v)) := by
  intro i p hp t
  rw [slow, Expression.eval_slow hO S.isOpen hG hQ v (hRs i) hp]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  have heq : (fun x => (R i).eval G (x, t)) =ᶠ[𝓝 p]
      (fun x => L (U.val x (t : CovarianceCorrector.Period))) := by
    filter_upwards [S.isOpen.mem_nhds hp] with x hx
    exact hR i x hx t
  rw [heq.fderiv_eq]
  have hU : DifferentiableAt ℝ (fun x => U.val x (t : CovarianceCorrector.Period)) p :=
    ((U.smooth.contDiffAt ((S.isOpen.prod isOpen_univ).mem_nhds ⟨hp, Set.mem_univ t⟩)).comp p
      (contDiff_id.prodMk contDiff_const).contDiffAt).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  change fderiv ℝ (L ∘ fun x => U.val x (t : CovarianceCorrector.Period)) p
    (coordinateVector v) = _
  rw [(L.hasFDerivAt.comp p hU.hasFDerivAt).fderiv]
  rw [Family.slow_apply U (coordinateVector v) hp t,
    ← LocalPeriodicCalculus.fderiv_slice S.isOpen U.smooth hp]
  rfl

lemma represents_angle {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) : Represents G R.angle U.angle := by
  intro i p hp t
  rw [angle, Expression.eval_angle hO (hRs i) G (hQ hp)]
  have heq : (fun s => (R i).eval G (p, s)) =
      (fun s : ℝ => U.val p (s : CovarianceCorrector.Period) i) := funext (hR i p hp)
  rw [heq]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  exact (L.hasFDerivAt.comp_hasDerivAt t (U.angle_hasDerivAt hp t)).deriv

lemma represents_mean {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) : Represents G R.mean U.vectorMean := by
  intro i p hp t
  rw [mean, Expression.eval_mean hO (hRs i) G (hQ hp)]
  simp only [hR i p hp, Family.vectorMean_apply]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  change (∫ s in (0 : ℝ)..1, L (U.val p (s : CovarianceCorrector.Period))) =
    L (CovarianceCorrector.average (U.val p))
  have hInt : IntervalIntegrable (fun s : ℝ => U.val p (s : CovarianceCorrector.Period))
      MeasureTheory.volume 0 1 :=
    ((U.val p).continuous.comp (AddCircle.continuous_mk' 1)).intervalIntegrable 0 1
  rw [L.intervalIntegral_comp_comm hInt, PeriodicPrimitive.integral_lift_eq_haar]
  rfl

lemma represents_primitive {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {R : VectorExpression} {U : Family S R4} (hRs : R.SmoothCoeffs O)
    (hR : Represents G R U) (hm : ∀ p ∈ S, CovarianceCorrector.average (U.val p) = 0) :
    Represents G R.primitive (U.primitive hm) := by
  intro i p hp t
  rw [primitive, Expression.eval_primitive hO (hRs i) G (hQ hp)]
  have heq : (fun s => (R i).eval G (p, s)) =
      (fun s : ℝ => U.val p (s : CovarianceCorrector.Period) i) := funext (hR i p hp)
  rw [heq, Family.primitive, Family.ofLocal_apply _ _ hp,
    LocalPeriodicCalculus.primitiveOn_apply _ _ _ _ _ hp]
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj i
  exact (primitive_map L ((U.val p).continuous.comp (AddCircle.continuous_mk' 1)) t).symm

end VectorExpression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialCorrectorSystem
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete periodic system with its explicit solution retained in the
family interface, for propagation of polynomial coefficient representations. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus
variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}
namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

theorem exists_system_formula (h j e : Family O ℝ)
    (hh : ∀ p ∈ O, average (h.val p) = 0) (hj : ∀ p ∈ O, average (j.val p) = 0)
    (he : ∀ p ∈ O, average (e.val p) = 0) :
    ∃ U : Family O E, (∀ p ∈ O, average (U.val p) = 0) ∧
      g.transverse.inner U.angle = h ∧
      g.transverse.inner (U.slow v) = j ∧
      (g.longitudinal.inner U.angle).fluct = e ∧
      (∀ Z : Set A, IsOpen Z → Z ⊆ O → (∀ p ∈ Z, h.val p = 0) →
        (∀ p ∈ Z, j.val p = 0) → (∀ p ∈ Z, e.val p = 0) → ∀ p ∈ Z, U.val p = 0) ∧
      (∀ p ∈ O, ∀ t : ℝ, U.val p (t : Period) =
        PeriodicCorrector.fullSolutionFormula v g.Y g.C g.X₀ g.V.val g.q h.val j.val e.val (p, t)) := by
  obtain ⟨U, D, hUs, _, hU0, hUd, hYd, hYs, hX, hzero, hformula⟩ :=
    PeriodicCorrector.solve_full_smooth_family_on_formula O O.isOpen v g.plane g.Y g.C g.X₀
      g.smoothY g.smoothC g.smoothX₀ g.derivativeY g.gram_ne
      g.perpY g.perpC g.perpX₀ g.V.val g.V_mem g.V.smooth
      g.q g.smoothq g.q_pos g.circle h.val j.val e.val h.smooth j.smooth e.smooth hh hj he
  let U' : Family O E := Family.ofLocal U hUs
  have hval (p : A) (hp : p ∈ O) : U'.val p = U p := by
    ext t
    exact Family.ofLocal_apply U hUs hp t
  have hangle (p : A) (hp : p ∈ O) (t : Period) : U'.angle.val p t = D p t := by
    refine Quotient.inductionOn' t ?_
    intro x
    have hd := U'.angle_hasDerivAt hp x
    simp only [hval p hp] at hd
    exact hd.unique (hUd p hp x)
  refine ⟨U', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hval p hp]
    exact hU0 p hp
  · ext p hp t
    simp only [Family.inner_apply, transverse, Family.constant_apply _ _ hp, hangle p hp]
    exact hYd p hp t
  · ext p hp t
    refine Quotient.inductionOn' t ?_
    intro x
    simp only [Family.inner_apply, transverse, Family.constant_apply _ _ hp, Family.slow_apply _ _ hp]
    rw [← fderiv_slice O.isOpen U'.smooth hp]
    have hv : (fun q => U'.val q (x : Period)) =ᶠ[𝓝 p] fun q => U q (x : Period) := by
      filter_upwards [O.isOpen.mem_nhds hp] with q hq
      rw [hval q hq]
    rw [hv.fderiv_eq, fderiv_slice O.isOpen hUs hp]
    exact hYs p hp x
  · ext p hp t
    have hinner : (g.longitudinal.inner U'.angle).val p =
        ⟨fun t => inner ℝ (g.X₀ p + g.V.val p t) (D p t),
          (continuous_const.add (g.V.val p).continuous).inner (D p).continuous⟩ := by
      ext s
      simp only [Family.inner_apply, longitudinal, Family.add_apply, Family.constant_apply _ _ hp, hangle p hp]
      rfl
    simp only [Family.fluct_apply, fluctuation, hinner]
    exact congrFun (hX p hp) t
  · intro Z hZ hZO hhZ hjZ heZ p hp
    rw [hval p (hZO hp)]
    exact hzero Z hZ hZO hhZ hjZ heZ p hp

  · intro p hp t
    rw [hval p hp]
    exact hformula p hp t

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialCorrectorRepresentation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual periodic system admits the polynomial solution whose order
bounds were established in JetPolynomialFullCorrector. -/
noncomputable section
open scoped ContDiff Topology

namespace ClosedSurfaceR4.JetPolynomial
open CovarianceCorrector LocalPeriodicExpansion

/-- The family solving the complete periodic system has the represented
four-coordinate correction. All equations and the zero-support property
are retained from the actual periodic solver. -/
theorem exists_polynomial_system {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) (v : Fin 2) (g : Geometry (E := R4) S (coordinateVector v))
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (hYg : ∀ p ∈ S, g.Y p = Y (lowJet G p))
    (hCg : ∀ p ∈ S, g.C p = C (lowJet G p))
    (hXg : ∀ p ∈ S, g.X₀ p = X₀ (lowJet G p))
    (hVg : ∀ p ∈ S, g.V.val p = V (lowJet G p))
    (hqg : ∀ p ∈ S, g.q p = q (lowJet G p))
    {h j e : Expression} (hh : h.SmoothCoeffs O) (hj : j.SmoothCoeffs O) (he : e.SmoothCoeffs O)
    (hf jf ef : Family S ℝ)
    (hhr : ∀ p ∈ S, ∀ t : ℝ, h.eval G (p, t) = hf.val p (t : Period))
    (hjr : ∀ p ∈ S, ∀ t : ℝ, j.eval G (p, t) = jf.val p (t : Period))
    (her : ∀ p ∈ S, ∀ t : ℝ, e.eval G (p, t) = ef.val p (t : Period))
    (hh0 : ∀ p ∈ S, average (hf.val p) = 0)
    (hj0 : ∀ p ∈ S, average (jf.val p) = 0)
    (he0 : ∀ p ∈ S, average (ef.val p) = 0) :
    ∃ U : Family S R4,
      (∀ p ∈ S, average (U.val p) = 0) ∧
      g.transverse.inner U.angle = hf ∧
      g.transverse.inner (U.slow (coordinateVector v)) = jf ∧
      (g.longitudinal.inner U.angle).fluct = ef ∧
      (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, hf.val p = 0) →
        (∀ p ∈ Z, jf.val p = 0) → (∀ p ∈ Z, ef.val p = 0) → ∀ p ∈ Z, U.val p = 0) ∧
      VectorExpression.Represents G
        (fun i => Expression.fullComponent Y C X₀ V q (EuclideanSpace.proj i) v h j e) U := by
  obtain ⟨U, hU0, hUa, hUs, hUfl, hUz, hform⟩ := g.exists_system_formula hf jf ef hh0 hj0 he0
  refine ⟨U, hU0, hUa, hUs, hUfl, hUz, ?_⟩
  intro i p hp t
  rw [Expression.eval_fullComponent hO S.isOpen hY hC hX hV hd hq hqp hcircle
    (EuclideanSpace.proj i) v hh hj he hG hQ hf.val jf.val ef.val hhr hjr her hp]
  change (EuclideanSpace.proj i) (PeriodicCorrector.fullSolutionFormula (coordinateVector v)
    (fun x => Y (lowJet G x)) (fun x => C (lowJet G x)) (fun x => X₀ (lowJet G x))
    (fun x => V (lowJet G x)) (fun x => q (lowJet G x)) hf.val jf.val ef.val (p, t)) =
      (EuclideanSpace.proj i) (U.val p (t : Period))
  rw [hform p hp t]
  unfold PeriodicCorrector.fullSolutionFormula
  rw [hYg p hp, hCg p hp, hXg p hp, hVg p hp, hqg p hp]

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

lemma smoothCoeffs_scale {O : Set LowJet} (a : ℝ) {e : Expression} (he : e.SmoothCoeffs O) :
    (e.scale a).SmoothCoeffs O := smoothCoeffs_map e _ (fun _ hc => contDiffOn_const.mul hc) he

lemma represents_add {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {e f : Expression} {U W : Family S ℝ} (he : Represents G e U) (hf : Represents G f W) :
    Represents G (.add e f) (U + W) := by
  intro p hp t
  simp only [eval, he p hp t, hf p hp t, Family.add_apply]

lemma represents_scale {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {e : Expression} {U : Family S ℝ} (he : Represents G e U) (a : ℝ) :
    Represents G (e.scale a) (a • U) := by
  intro p hp t
  simp only [eval_scale, he p hp t, Family.smul_apply, smul_eq_mul]

lemma represents_fluct {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O)
    {e : Expression} {U : Family S ℝ} (hs : e.SmoothCoeffs O) (he : Represents G e U) :
    Represents G e.fluct U.fluct := by
  intro p hp t
  rw [eval_fluct hO hs G (hQ hp)]
  simp only [he p hp, Family.fluct_apply, fluctuation]
  rw [PeriodicPrimitive.integral_lift_eq_haar]
  rfl

lemma represents_sumFinset {ι : Type*} {S : TopologicalSpace.Opens Base} {G : Base → Space}
    (a : Finset ι) {e : ι → Expression} {U : ι → Family S ℝ}
    (he : ∀ i ∈ a, Represents G (e i) (U i)) :
    Represents G (sumFinset a e) (∑ i ∈ a, U i) := by
  classical
  intro p hp t
  rw [sumFinset, eval_sumList, ← List.sum_toFinset _ a.nodup_toList, Finset.toList_toFinset,
    Family.sum_apply]
  exact Finset.sum_congr rfl (fun i hi => he i hi p hp t)

lemma smoothCoeffs_sumFinset {ι : Type*} {O : Set LowJet} (a : Finset ι) (e : ι → Expression)
    (he : ∀ i ∈ a, (e i).SmoothCoeffs O) : (sumFinset a e).SmoothCoeffs O := by
  apply smoothCoeffs_sumList
  intro i hi
  exact he i (Finset.mem_toList.mp hi)

lemma represents_dot {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : VectorExpression.Represents G R U)
    (hT : VectorExpression.Represents G T W) : Represents G (R.dot T) (U.inner W) := by
  intro p hp t
  rw [VectorExpression.eval_dot hR hT hp, Family.inner_apply]

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialCancellation
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial forcing gives a polynomial correction cancelling the actual
three metric fluctuations, with the support guarantee retained. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open CovarianceCorrector LocalPeriodicExpansion

theorem exists_polynomial_cancellation {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) (v : Fin 2) (g : Geometry (E := R4) S (coordinateVector v))
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (hYg : ∀ p ∈ S, g.Y p = Y (lowJet G p))
    (hCg : ∀ p ∈ S, g.C p = C (lowJet G p))
    (hXg : ∀ p ∈ S, g.X₀ p = X₀ (lowJet G p))
    (hVg : ∀ p ∈ S, g.V.val p = V (lowJet G p))
    (hqg : ∀ p ∈ S, g.q p = q (lowJet G p))
    {b c d : Expression} (hb : b.SmoothCoeffs O) (hc : c.SmoothCoeffs O) (hdp : d.SmoothCoeffs O)
    (bf cf df : Family S ℝ)
    (hbr : Expression.Represents G b bf) (hcr : Expression.Represents G c cf)
    (hdr : Expression.Represents G d df) :
    ∃ U : Family S R4,
      (∀ p ∈ S, average (U.val p) = 0) ∧
      (g.transverse.inner U.angle + bf).fluct = 0 ∧
      (g.longitudinal.inner U.angle + cf).fluct = 0 ∧
      ((2 : ℝ) • g.transverse.inner (U.slow (coordinateVector v)) + df).fluct = 0 ∧
      (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, bf.val p = 0) →
        (∀ p ∈ Z, cf.val p = 0) → (∀ p ∈ Z, df.val p = 0) → ∀ p ∈ Z, U.val p = 0) ∧
      VectorExpression.Represents G
        (fun i => Expression.fullComponent Y C X₀ V q (EuclideanSpace.proj i) v
          (b.fluct.scale (-1)) (d.fluct.scale (-1 / 2)) (c.fluct.scale (-1))) U := by
  have hmean (a : ℝ) (f : Family S ℝ) (p : Base) (_ : p ∈ S) :
      average ((a • f.fluct).val p) = 0 := by
    change average (fun t => a • f.fluct.val p t) = 0
    rw [average_const_smul, f.fluct_mean_zero, smul_zero]
  have hbs := Expression.smoothCoeffs_scale (-1) (Expression.smoothCoeffs_fluct hO hb)
  have hcs := Expression.smoothCoeffs_scale (-1) (Expression.smoothCoeffs_fluct hO hc)
  have hds := Expression.smoothCoeffs_scale (-1 / 2) (Expression.smoothCoeffs_fluct hO hdp)
  have hbr' := Expression.represents_scale (Expression.represents_fluct hO hQ hb hbr) (-1)
  have hcr' := Expression.represents_scale (Expression.represents_fluct hO hQ hc hcr) (-1)
  have hdr' := Expression.represents_scale (Expression.represents_fluct hO hQ hdp hdr) (-1 / 2)
  obtain ⟨U, hU0, hYf, hYs, hXf, hzero, hrep⟩ := exists_polynomial_system hO v g
    hY hC hX hV hd hq hqp hcircle hG hQ hYg hCg hXg hVg hqg hbs hds hcs
    ((-1 : ℝ) • bf.fluct) ((-1 / 2 : ℝ) • df.fluct) ((-1 : ℝ) • cf.fluct)
    hbr' hdr' hcr' (hmean _ _) (hmean _ _) (hmean _ _)
  refine ⟨U, hU0, ?_, ?_, ?_, ?_, hrep⟩
  · rw [Family.fluct_add, hYf, Family.fluct_smul, Family.fluct_fluct]
    module
  · rw [Family.fluct_add, hXf]
    module
  · rw [Family.fluct_add, Family.fluct_smul, hYs, Family.fluct_smul, Family.fluct_fluct]
    module
  · intro Z hZ hZS hbZ hcZ hdZ
    have hz (a : ℝ) (f : Family S ℝ) (hf : ∀ p ∈ Z, f.val p = 0) :
        ∀ p ∈ Z, (a • f.fluct).val p = 0 := by
      intro p hp
      change a • f.fluct.val p = 0
      rw [f.fluct_zero_at (hf p hp), smul_zero]
    exact hzero Z hZ hZS (hz _ _ hbZ) (hz _ _ hdZ) (hz _ _ hcZ)

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicMetricCoefficients
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Coefficients of the pullback metric of the finite periodic ansatz. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}



omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xCoefficient_congr {dx : A} {U W : ℕ → Family O E} {i : ℕ}
    (h₁ : U (i - 1) = W (i - 1)) (h₂ : U i = W i) :
    xCoefficient dx U i = xCoefficient dx W i := by
  simp only [xCoefficient, h₁, h₂]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yCoefficient_congr {dy : A} {U W : ℕ → Family O E} {i : ℕ}
    (h : U (i - 1) = W (i - 1)) : yCoefficient dy U i = yCoefficient dy W i := by
  simp only [yCoefficient, h]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxQuadratic_congr {dx : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i < r, U i = W i) : xxQuadratic dx U r = xxQuadratic dx W r := by
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  rw [xCoefficient_congr (h _ (by omega)) (h _ hir),
    xCoefficient_congr (h _ (by omega)) (h _ (by omega))]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyQuadratic_congr {dx dy : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i < r, U i = W i) : xyQuadratic dx dy U r = xyQuadratic dx dy W r := by
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  rw [xCoefficient_congr (h _ (by omega)) (h _ hir),
    yCoefficient_congr (h _ (by omega))]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyQuadratic_congr {dy : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i < r - 1, U i = W i) : yyQuadratic dy U r = yyQuadratic dy W r := by
  apply Finset.sum_congr rfl
  intro i hi
  obtain ⟨hi, hir⟩ := Finset.mem_Ico.mp hi
  rw [yCoefficient_congr (h _ (by omega)), yCoefficient_congr (h _ (by omega))]

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricCoefficients
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual coordinate polynomial expressions for the metric coefficients in
the finite oscillatory recursion. Index zero denotes the first correction. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

lemma represents_xCoefficient {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dx : Fin 2) (i : ℕ) :
    VectorExpression.Represents G (xCoefficient dx U i)
      (LocalPeriodicExpansion.xCoefficient (coordinateVector dx) W i) :=
  VectorExpression.represents_add
    (VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dx)
    (VectorExpression.represents_angle hO hQ (hUs _) (hU _))

lemma represents_yCoefficient {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dy : Fin 2) (i : ℕ) :
    VectorExpression.Represents G (yCoefficient dy U i)
      (LocalPeriodicExpansion.yCoefficient (coordinateVector dy) W i) :=
  VectorExpression.represents_slow hO hG hQ (hUs _) (hU _) dy

lemma represents_xxQuadratic {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dx : Fin 2) (r : ℕ) :
    Expression.Represents G (xxQuadratic dx U r)
      (LocalPeriodicExpansion.xxQuadratic (coordinateVector dx) W r) := by
  apply Expression.represents_sumFinset
  intro i _
  exact Expression.represents_dot (represents_xCoefficient hO hG hQ hUs hU dx i)
    (represents_xCoefficient hO hG hQ hUs hU dx (r - i))

lemma represents_xyQuadratic {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dx dy : Fin 2) (r : ℕ) :
    Expression.Represents G (xyQuadratic dx dy U r)
      (LocalPeriodicExpansion.xyQuadratic (coordinateVector dx) (coordinateVector dy) W r) := by
  apply Expression.represents_sumFinset
  intro i _
  exact Expression.represents_dot (represents_xCoefficient hO hG hQ hUs hU dx i)
    (represents_yCoefficient hO hG hQ hUs hU dy (r - i))

lemma represents_yyQuadratic {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {U : ℕ → VectorExpression} {W : ℕ → LocalPeriodicExpansion.Family S R4}
    (hUs : ∀ j, (U j).SmoothCoeffs O)
    (hU : ∀ j, VectorExpression.Represents G (U j) (W j)) (dy : Fin 2) (r : ℕ) :
    Expression.Represents G (yyQuadratic dy U r)
      (LocalPeriodicExpansion.yyQuadratic (coordinateVector dy) W r) := by
  apply Expression.represents_sumFinset
  intro i _
  exact Expression.represents_dot (represents_yCoefficient hO hG hQ hUs hU dy i)
    (represents_yCoefficient hO hG hQ hUs hU dy (r - i))

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialMetricForcing
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The right-hand sides of the finite triangular correction step are actual
higher-jet polynomials. Their maximal jet order is the preceding order plus one. -/
noncomputable section
open scoped ContDiff BigOperators

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial

lemma smooth_xCoefficient {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dx : Fin 2) (i : ℕ) :
    (xCoefficient dx U i).SmoothCoeffs O := by
  intro a
  exact ⟨Expression.smoothCoeffs_slow hO dx (hU _ _),
    Expression.smoothCoeffs_angle hO (hU _ _)⟩

lemma smooth_yCoefficient {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dy : Fin 2) (i : ℕ) :
    (yCoefficient dy U i).SmoothCoeffs O := by
  intro a
  exact Expression.smoothCoeffs_slow hO dy (hU _ _)

lemma smooth_xxQuadratic {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dx : Fin 2) (r : ℕ) :
    (xxQuadratic dx U r).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  exact VectorExpression.smoothCoeffs_dot (smooth_xCoefficient hO hU dx i)
    (smooth_xCoefficient hO hU dx (r - i))

lemma smooth_xyQuadratic {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dx dy : Fin 2) (r : ℕ) :
    (xyQuadratic dx dy U r).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  exact VectorExpression.smoothCoeffs_dot (smooth_xCoefficient hO hU dx i)
    (smooth_yCoefficient hO hU dy (r - i))

lemma smooth_yyQuadratic {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) (dy : Fin 2) (r : ℕ) :
    (yyQuadratic dy U r).SmoothCoeffs O := by
  apply Expression.smoothCoeffs_sumFinset
  intro i _
  exact VectorExpression.smoothCoeffs_dot (smooth_yCoefficient hO hU dy i)
    (smooth_yCoefficient hO hU dy (r - i))

lemma smooth_mixedForcing {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) {X Y : VectorExpression}
    (hX : X.SmoothCoeffs O) (hY : Y.SmoothCoeffs O) (dx dy : Fin 2) (r : ℕ) :
    (mixedForcing X Y dx dy U r).SmoothCoeffs O :=
  ⟨⟨VectorExpression.smoothCoeffs_dot hX (smooth_yCoefficient hO hU dy r),
    VectorExpression.smoothCoeffs_dot hY (fun a => Expression.smoothCoeffs_slow hO dx (hU _ a))⟩,
    smooth_xyQuadratic hO hU dx dy r⟩

lemma smooth_longitudinalForcing {O : Set LowJet} (hO : IsOpen O) {U : ℕ → VectorExpression}
    (hU : ∀ j, (U j).SmoothCoeffs O) {X : VectorExpression}
    (hX : X.SmoothCoeffs O) (dx : Fin 2) (r : ℕ) :
    (longitudinalForcing X dx U r).SmoothCoeffs O :=
  ⟨VectorExpression.smoothCoeffs_dot hX (fun a => Expression.smoothCoeffs_slow hO dx (hU _ a)),
    Expression.smoothCoeffs_scale _ (smooth_xxQuadratic hO hU dx r)⟩

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialJetSmoothness
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite correction expressions have coefficients smooth throughout
the admissible low-jet domain. No higher jets occur in coefficient inverses. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open CovarianceCorrector

lemma smooth_longitudinal {O : Set LowJet} {X₀ : LowJet → R4} {V : LowJet → C(Period, R4)}
    (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ)) :
    (longitudinal X₀ V).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  exact L.contDiff.comp_contDiffOn
    ((hX.comp contDiffOn_fst (fun _ hz => hz.1)).add hV)

lemma smooth_transverse {O : Set LowJet} {Y : LowJet → R4} (hY : ContDiffOn ℝ ∞ Y O) :
    (transverse Y).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  have hi : ContDiffOn ℝ ∞ (fun Q => Y Q a) O :=
    L.contDiff.comp_contDiffOn hY
  exact hi.comp contDiffOn_fst (fun _ hz => hz.1)

lemma smooth_initial {O : Set LowJet} (hO : IsOpen O) {V : LowJet → C(Period, R4)}
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ)) :
    (initial V).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  have hc : (Expression.coeff (fun z => V z.1 (z.2 : Period) a)).SmoothCoeffs O :=
    L.contDiff.comp_contDiffOn hV
  exact Expression.smoothCoeffs_primitive hO (Expression.smoothCoeffs_fluct hO hc)

lemma smooth_step {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    {U : ℕ → VectorExpression} (hU : ∀ j, (U j).SmoothCoeffs O) (dx dy : Fin 2) (r : ℕ) :
    (step Y C X₀ V q dx dy U r).SmoothCoeffs O := by
  intro a
  apply Expression.smoothCoeffs_fullComponent hO hY hC hX hV hd hq hqp hcircle (EuclideanSpace.proj a) dy
  · exact Expression.smoothCoeffs_scale _ (Expression.smoothCoeffs_fluct hO
      (smooth_mixedForcing hO hU (smooth_longitudinal hX hV) (smooth_transverse hY) dx dy r))
  · exact Expression.smoothCoeffs_scale _ (Expression.smoothCoeffs_fluct hO (smooth_yyQuadratic hO hU dy (r + 1)))
  · exact Expression.smoothCoeffs_scale _ (Expression.smoothCoeffs_fluct hO
      (smooth_longitudinalForcing hO hU (smooth_longitudinal hX hV) dx r))

theorem coefficients_smooth {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (dx dy : Fin 2) (n i : ℕ) :
    (coefficients Y C X₀ V q dx dy n i).SmoothCoeffs O := by
  induction n generalizing i with
  | zero => exact smooth_initial hO hV
  | succ n ih =>
    by_cases hi : i = n + 1
    · subst i
      rw [coefficients, Function.update_self]
      exact smooth_step hO hY hC hX hV hd hq hqp hcircle ih dx dy (n + 1)
    · rw [coefficients, Function.update_of_ne hi]
      exact ih i

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicExpansionInit
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
attribute [-simp] _root_.ContinuousLinearMap.comp_toSpanSingleton_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopX_zero _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_apply _root_.OAI.ClosedSurfaceR4.CollarVelocity.loopY_zero _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss_covariance _root_.OAI.ClosedSurfaceR4.JetPolynomial.Expression.order_covariance _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.global_apply _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xTangent_zero _root_.OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yTangent_zero _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.add_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.angle_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.constant_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.fluct_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.inner_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.mean_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.neg_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.slow_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.smul_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sub_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.sum_apply _root_.OAI.ClosedSurfaceR4.PeriodicExpansion.Family.zero_apply _root_.Path.extend_div_self
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Initial coefficient and transverse cancellation on the admissible domain. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.LocalPeriodicExpansion
open CovarianceCorrector LocalPeriodicCalculus

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry
variable {v : A} (g : Geometry (E := E) O v)

omit [FiniteDimensional ℝ E] in
lemma initial_mean_zero {p : A} (hp : p ∈ O) : average (g.initial.val p) = 0 :=
  Family.primitive_mean_zero _ _ hp

lemma initial_mem {p : A} (hp : p ∈ O) (t : Period) : g.initial.val p t ∈ g.plane p := by
  apply Family.primitive_mem _ _ _ _ hp
  intro q hq s
  simp only [Family.sub_apply, Family.vectorMean_apply]
  exact (g.plane q).sub_mem (g.V_mem q hq s)
    (average_mem_submodule (g.plane q) (g.V.val q).continuous (g.V_mem q hq))

lemma initial_pairing {p : A} (hp : p ∈ O) (t : Period) :
    inner ℝ (g.Y p) (g.initial.val p t) = 0 ∧
      inner ℝ (g.C p) (g.initial.val p t) = 0 :=
  ⟨g.perpY p hp _ (g.initial_mem hp t), g.perpC p hp _ (g.initial_mem hp t)⟩

lemma initial_transverse_derivative : g.transverse.inner (g.initial.slow v) = 0 := by
  ext p hp t
  refine Quotient.inductionOn' t ?_
  intro x
  simp only [Family.inner_apply, transverse, Family.constant_apply _ _ hp,
    Family.slow_apply _ _ hp, Family.zero_apply]
  have hUt : ContDiffAt ℝ ∞ (fun q => g.initial.val q (x : Period)) p :=
    (g.initial.smooth.contDiffAt ((O.isOpen.prod isOpen_univ).mem_nhds
      ⟨hp, Set.mem_univ x⟩)).comp p (contDiff_id.prodMk contDiff_const).contDiffAt
  have hd := PeriodicCorrector.directional_pairing_constraint_on O.isOpen hp
    ((g.smoothY.contDiffAt (O.isOpen.mem_nhds hp)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))
    (hUt.differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)) (differentiableAt_const (c := (0 : ℝ)))
    (fun q hq => (g.initial_pairing hq (x : Period)).1) (g.derivativeY p hp)
    (show inner ℝ (g.C p) (g.initial.val p (x : Period)) =
        fderiv ℝ (fun _ : A => (0 : ℝ)) p v - 0 by
      simpa using (g.initial_pairing hp (x : Period)).2)
  rwa [fderiv_slice O.isOpen g.initial.smooth hp] at hd

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialGeometry
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Low-jet geometry and the initial primitive in the actual periodic family
are represented by the corresponding coordinate polynomial expressions. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion CovarianceCorrector

namespace VectorExpression

lemma represents_sub {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {R T : VectorExpression} {U W : Family S R4} (hR : Represents G R U)
    (hT : Represents G T W) : Represents G (R.sub T) (U - W) := by
  intro i p hp t
  simp only [sub, Expression.eval_sub, hR i p hp t, hT i p hp t, Family.sub_apply]
  rfl

end VectorExpression

namespace MetricPolynomial

lemma represents_longitudinal {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {v : Base} (g : Geometry (E := R4) S v) (X₀ : LowJet → R4) (V : LowJet → C(Period, R4))
    (hX : ∀ p ∈ S, g.X₀ p = X₀ (lowJet G p)) (hV : ∀ p ∈ S, g.V.val p = V (lowJet G p)) :
    VectorExpression.Represents G (longitudinal X₀ V) g.longitudinal := by
  intro i p hp t
  change (X₀ (lowJet G p) + V (lowJet G p) (t : Period)) i = _
  rw [Geometry.longitudinal, Family.add_apply, Family.constant_apply _ _ hp,
    hX p hp, hV p hp]

lemma represents_transverse {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {v : Base} (g : Geometry (E := R4) S v) (Y : LowJet → R4)
    (hY : ∀ p ∈ S, g.Y p = Y (lowJet G p)) :
    VectorExpression.Represents G (transverse Y) g.transverse := by
  intro i p hp t
  change Y (lowJet G p) i = _
  rw [Geometry.transverse, Family.constant_apply _ _ hp, hY p hp]

lemma represents_velocity {S : TopologicalSpace.Opens Base} {G : Base → Space}
    {v : Base} (g : Geometry (E := R4) S v) (V : LowJet → C(Period, R4))
    (hV : ∀ p ∈ S, g.V.val p = V (lowJet G p)) :
    VectorExpression.Represents G (velocity V) g.V := by
  intro i p hp t
  change V (lowJet G p) (t : Period) i = _
  rw [hV p hp]

lemma smooth_velocity {O : Set LowJet} {V : LowJet → C(Period, R4)}
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ)) :
    (velocity V).SmoothCoeffs O := by
  intro a
  let L : R4 →L[ℝ] ℝ := EuclideanSpace.proj a
  exact L.contDiff.comp_contDiffOn hV

lemma represents_initial {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hQ : Set.MapsTo (lowJet G) S O) {v : Base}
    (g : Geometry (E := R4) S v) {V : LowJet → C(Period, R4)}
    (hVs : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hV : ∀ p ∈ S, g.V.val p = V (lowJet G p)) :
    VectorExpression.Represents G (initial V) g.initial := by
  have hs := smooth_velocity hVs
  have hv := represents_velocity g V hV
  have hm := VectorExpression.represents_mean hO hQ hs hv
  have hc := VectorExpression.represents_sub hv hm
  have hcs : ((velocity V).sub (velocity V).mean).SmoothCoeffs O := by
    intro a
    exact Expression.smoothCoeffs_fluct hO (hs a)
  exact VectorExpression.represents_primitive hO hQ hcs hc (fun p _ => g.V.centered_mean_zero p)

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialForcingRepresentation
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The polynomial right-hand sides coincide with those in the actual
triangular metric-cancellation recursion. -/
noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open LocalPeriodicExpansion

lemma represents_mixedForcing {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    {X Y : VectorExpression} {Xf Yf : Family S R4}
    (hX : VectorExpression.Represents G X Xf) (hY : VectorExpression.Represents G Y Yf)
    (dx dy : Fin 2) (r : ℕ) :
    Expression.Represents G (mixedForcing X Y dx dy R r)
      (Xf.inner (LocalPeriodicExpansion.yCoefficient (coordinateVector dy) U r) +
        Yf.inner ((U (r - 1)).slow (coordinateVector dx)) +
        LocalPeriodicExpansion.xyQuadratic (coordinateVector dx) (coordinateVector dy) U r) :=
  Expression.represents_add (Expression.represents_add
    (Expression.represents_dot hX (represents_yCoefficient hO hG hQ hRs hR dy r))
    (Expression.represents_dot hY (VectorExpression.represents_slow hO hG hQ (hRs _) (hR _) dx)))
    (represents_xyQuadratic hO hG hQ hRs hR dx dy r)

lemma represents_longitudinalForcing {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    {X : VectorExpression} {Xf : Family S R4}
    (hX : VectorExpression.Represents G X Xf) (dx : Fin 2) (r : ℕ) :
    Expression.Represents G (longitudinalForcing X dx R r)
      (Xf.inner ((U (r - 1)).slow (coordinateVector dx)) +
        (1 / 2 : ℝ) • LocalPeriodicExpansion.xxQuadratic (coordinateVector dx) U r) :=
  Expression.represents_add
    (Expression.represents_dot hX (VectorExpression.represents_slow hO hG hQ (hRs _) (hR _) dx))
    (Expression.represents_scale (represents_xxQuadratic hO hG hQ hRs hR dx r) (1 / 2))

lemma represents_transverseForcing {S : TopologicalSpace.Opens Base} {O : Set LowJet} (hO : IsOpen O)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    {R : ℕ → VectorExpression} {U : ℕ → Family S R4}
    (hRs : ∀ i, (R i).SmoothCoeffs O) (hR : ∀ i, VectorExpression.Represents G (R i) (U i))
    (dy : Fin 2) (r : ℕ) :
    Expression.Represents G (transverseForcing dy R r)
      (LocalPeriodicExpansion.yyQuadratic (coordinateVector dy) U (r + 1)) :=
  represents_yyQuadratic hO hG hQ hRs hR dy (r + 1)

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicCoefficientSupport
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Differentiating and forming metric coefficients preserves local zero support. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

variable {Z : Set A} (hO : IsOpen Z) (hZO : Z ⊆ O) (U : ℕ → Family O E)
  (hU : ∀ i p, p ∈ Z → (U i).val p = 0)

include hO hU hZO

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xCoefficient_zero_on (dx : A) (i : ℕ) {p : A} (hp : p ∈ Z) :
    (xCoefficient dx U i).val p = 0 := by
  have hs := (U (i - 1)).slow_zero_on hO (hU (i - 1)) dx (hZO hp) hp
  have ha := (U i).angle_zero_at (hZO hp) (hU i p hp)
  ext t
  change ((U (i - 1)).slow dx).val p t + (U i).angle.val p t = 0
  rw [hs, ha]
  simp only [ContinuousMap.zero_apply, add_zero]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yCoefficient_zero_on (dy : A) (i : ℕ) {p : A} (hp : p ∈ Z) :
    (yCoefficient dy U i).val p = 0 :=
  (U (i - 1)).slow_zero_on hO (hU (i - 1)) dy (hZO hp) hp

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxQuadratic_zero_on (dx : A) (r : ℕ) {p : A} (hp : p ∈ Z) :
    (xxQuadratic dx U r).val p = 0 := by
  ext t
  simp only [xxQuadratic, Family.sum_apply, Family.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [xCoefficient_zero_on hO hZO U hU dx i hp]
  exact inner_zero_left _

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyQuadratic_zero_on (dx dy : A) (r : ℕ) {p : A} (hp : p ∈ Z) :
    (xyQuadratic dx dy U r).val p = 0 := by
  ext t
  simp only [xyQuadratic, Family.sum_apply, Family.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [xCoefficient_zero_on hO hZO U hU dx i hp]
  exact inner_zero_left _

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyQuadratic_zero_on (dy : A) (r : ℕ) {p : A} (hp : p ∈ Z) :
    (yyQuadratic dy U r).val p = 0 := by
  ext t
  simp only [yyQuadratic, Family.sum_apply, Family.inner_apply]
  apply Finset.sum_eq_zero
  intro i hi
  rw [yCoefficient_zero_on hO hZO U hU dy i hp]
  exact inner_zero_left _

end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Primitive_LocalPeriodicTriangularRecursion
attribute [-instance] _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite triangular recursion for the angle-independent metric coefficients. -/

noncomputable section
open scoped BigOperators

namespace ClosedSurfaceR4.LocalPeriodicExpansion

open CovarianceCorrector

variable {A E : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  {O : TopologicalSpace.Opens A}

namespace Geometry

variable {dy : A} (g : Geometry (E := E) O dy)

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xxCoefficient_congr {dx : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i ≤ r, U i = W i) : g.xxCoefficient dx U r = g.xxCoefficient dx W r := by
  unfold xxCoefficient
  rw [xCoefficient_congr (h _ (by omega)) (h _ le_rfl),
    xxQuadratic_congr (fun i hi => h i (by omega))]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma xyCoefficient_congr {dx : A} {U W : ℕ → Family O E} {r : ℕ}
    (h : ∀ i ≤ r, U i = W i) : g.xyCoefficient dx U r = g.xyCoefficient dx W r := by
  unfold xyCoefficient
  rw [xCoefficient_congr (h _ (by omega)) (h _ le_rfl),
    yCoefficient_congr (h _ (by omega)), xyQuadratic_congr (fun i hi => h i (by omega))]

omit [FiniteDimensional ℝ A] [CompleteSpace E] [FiniteDimensional ℝ E] in
lemma yyCoefficient_congr {U W : ℕ → Family O E} {r : ℕ}
    (hr : 0 < r) (h : ∀ i < r, U i = W i) : g.yyCoefficient U r = g.yyCoefficient W r := by
  unfold yyCoefficient
  rw [yCoefficient_congr (h _ (by omega)), yyQuadratic_congr (fun i hi => h i (by omega))]

end Geometry
end ClosedSurfaceR4.LocalPeriodicExpansion

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialAdvance
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual triangular correction step, retaining its polynomial representation. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open CovarianceCorrector LocalPeriodicExpansion

theorem polynomial_advance {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) (v : Fin 2) (g : Geometry (E := R4) S (coordinateVector v))
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (hYg : ∀ p ∈ S, g.Y p = Y (lowJet G p))
    (hCg : ∀ p ∈ S, g.C p = C (lowJet G p))
    (hXg : ∀ p ∈ S, g.X₀ p = X₀ (lowJet G p))
    (hVg : ∀ p ∈ S, g.V.val p = V (lowJet G p))
    (hqg : ∀ p ∈ S, g.q p = q (lowJet G p))
    (dxIndex : Fin 2) (U : ℕ → Family S R4) (R : ℕ → VectorExpression) (r : ℕ) (hr : 0 < r)
    (hU : ∀ i p, p ∈ S → average ((U i).val p) = 0)
    (hRs : ∀ i, (R i).SmoothCoeffs O)
    (hR : ∀ i, VectorExpression.Represents G (R i) (U i)) :
    ∃ W : ℕ → Family S R4,
      (∀ i < r, W i = U i) ∧ (∀ i p, p ∈ S → average ((W i).val p) = 0) ∧
      (g.xxCoefficient (coordinateVector dxIndex) W r).fluct = 0 ∧
      (g.xyCoefficient (coordinateVector dxIndex) W r).fluct = 0 ∧
      (g.yyCoefficient W (r + 1)).fluct = 0 ∧
      (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ i p, p ∈ Z → (U i).val p = 0) →
        ∀ i p, p ∈ Z → (W i).val p = 0) ∧
      (∀ i, VectorExpression.Represents G
        (Function.update R r (MetricPolynomial.step Y C X₀ V q dxIndex v R r) i) (W i)) := by
  let dx : Base := coordinateVector dxIndex
  let dy : Base := coordinateVector v
  let b := g.longitudinal.inner (yCoefficient dy U r) +
    g.transverse.inner ((U (r - 1)).slow dx) + xyQuadratic dx dy U r
  let c := g.longitudinal.inner ((U (r - 1)).slow dx) +
    (1 / 2 : ℝ) • xxQuadratic dx U r
  let d := yyQuadratic dy U (r + 1)
  let pb := MetricPolynomial.mixedForcing (MetricPolynomial.longitudinal X₀ V)
    (MetricPolynomial.transverse Y) dxIndex v R r
  let pc := MetricPolynomial.longitudinalForcing (MetricPolynomial.longitudinal X₀ V) dxIndex R r
  let pd := MetricPolynomial.transverseForcing v R r
  have hlong := MetricPolynomial.represents_longitudinal g X₀ V hXg hVg
  have htrans := MetricPolynomial.represents_transverse g Y hYg
  have hpbr : Expression.Represents G pb b :=
    MetricPolynomial.represents_mixedForcing hO hG hQ hRs hR hlong htrans dxIndex v r
  have hpcr : Expression.Represents G pc c :=
    MetricPolynomial.represents_longitudinalForcing hO hG hQ hRs hR hlong dxIndex r
  have hpdr : Expression.Represents G pd d :=
    MetricPolynomial.represents_transverseForcing hO hG hQ hRs hR v r
  have hpbs : pb.SmoothCoeffs O := MetricPolynomial.smooth_mixedForcing hO hRs
    (MetricPolynomial.smooth_longitudinal hX hV) (MetricPolynomial.smooth_transverse hY) dxIndex v r
  have hpcs : pc.SmoothCoeffs O := MetricPolynomial.smooth_longitudinalForcing hO hRs
    (MetricPolynomial.smooth_longitudinal hX hV) dxIndex r
  have hpds : pd.SmoothCoeffs O := MetricPolynomial.smooth_yyQuadratic hO hRs v (r + 1)
  obtain ⟨u, hu0, hb, hc, hd', hzero, hurep⟩ := exists_polynomial_cancellation hO v g
    hY hC hX hV hd hq hqp hcircle hG hQ hYg hCg hXg hVg hqg
    hpbs hpcs hpds b c d hpbr hpcr hpdr
  let W := Function.update U r u
  have hlow (i : ℕ) (hi : i < r) : W i = U i := by
    exact Function.update_of_ne (a := i) (a' := r) (by omega) u U
  have hprev : W (r - 1) = U (r - 1) := hlow _ (by omega)
  have hcur : W r = u := Function.update_self r u U
  have hA : xCoefficient dx W r = (U (r - 1)).slow dx + u.angle := by
    simp only [xCoefficient, hprev, hcur]
  have hB : yCoefficient dy W r = yCoefficient dy U r := yCoefficient_congr hprev
  have hB' : yCoefficient dy W (r + 1) = u.slow dy := by
    simp only [yCoefficient, Nat.add_sub_cancel, hcur]
  have hxx := xxQuadratic_congr (dx := dx) hlow
  have hxy := xyQuadratic_congr (dx := dx) (dy := dy) hlow
  have hyy : yyQuadratic dy W (r + 1) = d :=
    yyQuadratic_congr (fun i hi => hlow i (by omega))
  refine ⟨W, hlow, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i p hp
    by_cases hi : i = r
    · subst i
      rw [hcur]
      exact hu0 p hp
    · rw [show W i = U i from Function.update_of_ne hi u U]
      exact hU i p hp
  · have he : g.xxCoefficient dx W r =
        (2 : ℝ) • (g.longitudinal.inner u.angle + c) := by
      unfold Geometry.xxCoefficient c
      rw [hA, hxx, Family.inner_add_right]
      module
    rw [he, Family.fluct_smul, hc, smul_zero]
  · have he : g.xyCoefficient dx W r = g.transverse.inner u.angle + b := by
      unfold Geometry.xyCoefficient b
      rw [hA, hB, hxy, Family.inner_add_right]
      abel
    rw [he, hb]
  · change ((2 : ℝ) • g.transverse.inner (yCoefficient dy W (r + 1)) +
      yyQuadratic dy W (r + 1)).fluct = 0
    rw [hB', hyy]
    exact hd'
  · intro Z hO hZO hUO i p hp
    have huO : ∀ q ∈ Z, u.val q = 0 := by
      apply hzero Z hO hZO
      · intro q hq
        ext t
        have hs := (U (r - 1)).slow_zero_on hO (hUO (r - 1)) dx (hZO hq) hq
        simp only [b, Family.add_apply, Family.inner_apply,
          yCoefficient_zero_on hO hZO U hUO dy r hq, hs,
          xyQuadratic_zero_on hO hZO U hUO dx dy r hq,
          ContinuousMap.zero_apply, inner_zero_right, add_zero]
      · intro q hq
        ext t
        have hs := (U (r - 1)).slow_zero_on hO (hUO (r - 1)) dx (hZO hq) hq
        simp only [c, Family.add_apply, Family.smul_apply, Family.inner_apply,
          hs, xxQuadratic_zero_on hO hZO U hUO dx r hq,
          ContinuousMap.zero_apply, inner_zero_right, smul_zero, add_zero]
      · intro q hq
        exact yyQuadratic_zero_on hO hZO U hUO dy (r + 1) hq
    by_cases hi : i = r
    · subst i
      rw [hcur]
      exact huO p hp
    · rw [show W i = U i from Function.update_of_ne hi u U]
      exact hUO i p hp

  · intro i
    by_cases hi : i = r
    · subst i
      rw [Function.update_self, hcur]
      exact hurep
    · rw [Function.update_of_ne hi, show W i = U i from Function.update_of_ne hi u U]
      exact hR i

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_PolynomialCoefficientRecursion
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite smooth metric-cancelling coefficients with actual coordinate-jet
polynomial representations and the original support guarantee. -/
noncomputable section
open scoped ContDiff Topology
namespace ClosedSurfaceR4.JetPolynomial
open CovarianceCorrector LocalPeriodicExpansion

theorem exists_polynomial_coefficients_oai {S : TopologicalSpace.Opens Base} {O : Set LowJet}
    (hO : IsOpen O) (v : Fin 2) (g : Geometry (E := R4) S (coordinateVector v))
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hQ : Set.MapsTo (lowJet G) S O)
    (hYg : ∀ p ∈ S, g.Y p = Y (lowJet G p))
    (hCg : ∀ p ∈ S, g.C p = C (lowJet G p))
    (hXg : ∀ p ∈ S, g.X₀ p = X₀ (lowJet G p))
    (hVg : ∀ p ∈ S, g.V.val p = V (lowJet G p))
    (hqg : ∀ p ∈ S, g.q p = q (lowJet G p))
    (dxIndex : Fin 2) (n : ℕ) :
    ∃ U : ℕ → Family S R4,
      U 0 = g.initial ∧ (∀ i p, p ∈ S → average ((U i).val p) = 0) ∧
      (g.yyCoefficient U 1).fluct = 0 ∧
      (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, g.initial.val p = 0) →
        ∀ i p, p ∈ Z → (U i).val p = 0) ∧
      (∀ r, 1 ≤ r → r ≤ n →
        (g.xxCoefficient (coordinateVector dxIndex) U r).fluct = 0 ∧
        (g.xyCoefficient (coordinateVector dxIndex) U r).fluct = 0 ∧
        (g.yyCoefficient U (r + 1)).fluct = 0) ∧
      (∀ i, VectorExpression.Represents G
        (MetricPolynomial.coefficients Y C X₀ V q dxIndex v n i) (U i)) := by
  induction n with
  | zero =>
    refine ⟨fun _ => g.initial, rfl, fun _ _ hp => g.initial_mean_zero hp, ?_, ?_, ?_, ?_⟩
    · have hz : g.yyCoefficient (fun _ => g.initial) 1 = 0 := by
        simp only [Geometry.yyCoefficient, yCoefficient, yyQuadratic,
          Finset.Ico_self, Finset.sum_empty, g.initial_transverse_derivative, smul_zero, add_zero]
      rw [hz]
      ext p hp t
      simp only [Family.fluct_apply, CovarianceCorrector.fluctuation, Family.zero_apply]
      change (0 : ℝ) - average (fun _ => (0 : ℝ)) = 0
      rw [average_const, sub_self]
    · intro Z hZ hZS hz i p hp
      exact hz p hp
    · intro r hr hn
      omega
    · intro i
      exact MetricPolynomial.represents_initial hO hQ g hV hVg
  | succ n ih =>
    obtain ⟨U, hinit, hU, hy₁, hsupport, hcoeff, hrep⟩ := ih
    have hRs := MetricPolynomial.coefficients_smooth hO hY hC hX hV hd hq hqp hcircle dxIndex v n
    obtain ⟨W, hlow, hW, hxx, hxy, hyy, hzero, hWrep⟩ := polynomial_advance hO v g
      hY hC hX hV hd hq hqp hcircle hG hQ hYg hCg hXg hVg hqg
      dxIndex U (MetricPolynomial.coefficients Y C X₀ V q dxIndex v n) (n + 1) (by omega) hU hRs hrep
    refine ⟨W, (hlow 0 (by omega)).trans hinit, hW, ?_, ?_, ?_, ?_⟩
    · rw [g.yyCoefficient_congr (U := W) (W := U) (by omega : 0 < 1)
        (fun i hi => hlow i (by omega))]
      exact hy₁
    · intro Z hZ hZS hz
      exact hzero Z hZ hZS (hsupport Z hZ hZS hz)
    · intro r hr hn
      by_cases heq : r = n + 1
      · subst r
        exact ⟨hxx, hxy, hyy⟩
      · have hrn : r ≤ n := by omega
        obtain ⟨hx, hxy', hy⟩ := hcoeff r hr hrn
        rw [g.xxCoefficient_congr (fun i hi => hlow i (by omega)),
          g.xyCoefficient_congr (fun i hi => hlow i (by omega)),
          g.yyCoefficient_congr (by omega) (fun i hi => hlow i (by omega))]
        exact ⟨hx, hxy', hy⟩
    · exact hWrep

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.exists_polynomial_coefficients_oai := @OAI.ClosedSurfaceR4.JetPolynomial.exists_polynomial_coefficients_oai
