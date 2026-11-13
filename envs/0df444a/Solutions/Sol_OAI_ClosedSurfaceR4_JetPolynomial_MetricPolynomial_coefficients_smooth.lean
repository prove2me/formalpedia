-- Prove2me | solution 1 for OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:46:18.513324+00:00
-- url     : https://prove2.me/submissions/f4f0f4d3-b469-470b-99c2-ed3be1751ca7

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialIntegral
attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
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

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialLinear
attribute [-instance] _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.JetPolynomial.Expression

end

end OAI
end

section
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialOperations
attribute [-instance] _root_.instVAddIntReal_solutions
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

end ClosedSurfaceR4.JetPolynomial.Expression

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
-- module Solutions.OAIQ249_SI.SurfaceImmersion_Correction_JetPolynomialVector
attribute [-instance] _root_.instVAddIntReal_solutions
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

end VectorExpression
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

lemma smoothCoeffs_scale {O : Set LowJet} (a : ℝ) {e : Expression} (he : e.SmoothCoeffs O) :
    (e.scale a).SmoothCoeffs O := smoothCoeffs_map e _ (fun _ hc => contDiffOn_const.mul hc) he

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

theorem coefficients_smooth_oai {O : Set LowJet} (hO : IsOpen O)
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

theorem solution : type_of% @OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth_oai := @OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth_oai
