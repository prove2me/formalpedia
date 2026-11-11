-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:09.699597+00:00
-- url     : https://prove2.me/submissions/67ca1d93-7f51-4f44-921d-c030c40eadf9

import Mathlib
import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Piecewise
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ExtendedExponential
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.negLogCost_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ENNReal

namespace Invariant233

theorem negLogCost_extendedExpNeg (a : ℝ≥0∞) :
    negLogCost ((EReal.exp (-(a : EReal))).toReal) = a := by
  by_cases ha : a = ∞
  · simp [ha, negLogCost]
  · rw [extendedExpNeg_eq_exp_toReal a ha]
    simp only [negLogCost, Real.exp_ne_zero, ite_false, if_false,
      abs_of_pos (Real.exp_pos _), Real.log_exp, neg_neg]
    exact ENNReal.ofReal_toReal ha

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldPowerBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal

namespace InvariantProjection.FieldPowerBounds

variable {X E : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {μ : Measure X}

theorem ae_pow_apply (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : X → E →L[ℂ] E)
    (hT : ∀ ξ : Lp E 2 μ, ⇑(T ξ) =ᵐ[μ] fun x => A x (ξ x))
    (n : ℕ) (ξ : Lp E 2 μ) :
    ⇑((T ^ n) ξ) =ᵐ[μ] fun x => (A x ^ n) (ξ x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    filter_upwards [hT ((T ^ n) ξ), ih] with x hx hix
    rw [hx, hix, pow_succ', mul_apply_eq_comp]

end InvariantProjection.FieldPowerBounds

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal BigOperators
namespace Invariant233.WeightedShift

theorem operator_pow_apply_add (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) (k + n) =
      (∏ j ∈ Finset.range n, w (k + j)) * ξ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp, operator_apply]
    have hk : k + (↑(n + 1) : ℤ) - 1 = k + n := by omega
    rw [hk, ih, Finset.prod_range_succ]
    ring

theorem operator_pow_apply (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) k =
      (∏ j ∈ Finset.range n, w (k - n + j)) * ξ (k - n) := by
  simpa using operator_pow_apply_add w n ξ (k - n)

theorem norm_operator_pow_le (w : Weight) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ k : ℤ, ‖∏ j ∈ Finset.range n, w (k + j)‖ ≤ B) :
    ‖(operator w)^n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro ξ
  calc
    ‖((operator w)^n) ξ‖ ≤ ‖B • shift (n : ℤ) ξ‖ := by
      apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
      intro k
      simp only [operator_pow_apply, norm_mul, lp.coeFn_smul, Pi.smul_apply,
        norm_smul, Real.norm_eq_abs, abs_of_nonneg hB, shift_apply]
      exact mul_le_mul_of_nonneg_right (hprod (k - n)) (norm_nonneg _)
    _ = B * ‖ξ‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hB,
      (shift (n : ℤ)).norm_map]

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_QuasinilpotentSeries
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233

variable {A : Type*} [NormedRing A]

theorem NormQuasinilpotent.eventually_norm_pow_le {T : A}
    (hT : NormQuasinilpotent T) {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n : ℕ in atTop, ‖T ^ n‖ ≤ r ^ n := by
  have he := (tendsto_order.mp hT).2 r hr
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hnpos
  have hpow := pow_le_pow_left₀
    (Real.rpow_nonneg (norm_nonneg (T ^ n)) (1 / (n : ℝ))) hn.le n
  simpa only [one_div, Real.rpow_inv_natCast_pow (norm_nonneg (T ^ n))
    (Nat.ne_of_gt hnpos)] using hpow

variable [NormedAlgebra ℂ A]

theorem NormQuasinilpotent.summable_norm_smul_pow {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    Summable (fun n : ℕ => ‖z ^ n • T ^ n‖) := by
  let r : ℝ := 1 / (2 * (‖z‖ + 1))
  have hr : 0 < r := by dsimp [r] <;> positivity
  have hzr : ‖z‖ * r ≤ (1 / 2 : ℝ) := by
    dsimp [r]
    rw [mul_one_div, div_le_iff₀ (by positivity)]
    linarith [norm_nonneg z]
  apply (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).of_norm_bounded_eventually_nat
  filter_upwards [hT.eventually_norm_pow_le hr] with n hn
  rw [norm_norm, norm_smul, norm_pow]
  calc
    ‖z‖ ^ n * ‖T ^ n‖ ≤ ‖z‖ ^ n * r ^ n :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (‖z‖ * r) ^ n := (mul_pow _ _ _).symm
    _ ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ (by positivity) hzr n

variable [CompleteSpace A]

theorem NormQuasinilpotent.summable_smul_pow {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    Summable (fun n : ℕ => z ^ n • T ^ n) :=
  (hT.summable_norm_smul_pow z).of_norm

theorem NormQuasinilpotent.geometric_inverse_identities {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    (∑' n : ℕ, z ^ n • T ^ n) * (1 - z • T) = 1 ∧
      (1 - z • T) * (∑' n : ℕ, z ^ n • T ^ n) = 1 := by
  have hs : Summable (fun n : ℕ => (z • T) ^ n) := by
    simpa only [smul_pow] using hT.summable_smul_pow z
  constructor
  · simpa only [smul_pow] using hs.tsum_pow_mul_one_sub
  · simpa only [smul_pow] using hs.one_sub_mul_tsum_pow

theorem NormQuasinilpotent.inverse_one_sub_smul {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    Ring.inverse (1 - z • T) = ∑' n : ℕ, z ^ n • T ^ n := by
  have hi := hT.geometric_inverse_identities z
  let u : Aˣ := ⟨1 - z • T, (∑' n : ℕ, z ^ n • T ^ n), hi.2, hi.1⟩
  exact Ring.inverse_unit u

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldShiftMoments
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.WeightedShift

theorem inner_single_operator_pow_eq_zero (w : Weight) (n : ℕ) (hn : 0 < n)
    (k : ℤ) (a : ℂ) :
    inner ℂ (lp.single 2 k a) ((operator w ^ n) (lp.single 2 k a)) = 0 := by
  rw [lp.inner_single_left, operator_pow_apply]
  have hk : k - (n : ℤ) ≠ k := by omega
  simp [lp.single_apply, hk]

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem vectorTrace_const_pow_eq_zero
    (T : Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) (w : X → Weight)
    (hT : ∀ ξ : Lp Hilbert 2 μ, T ξ =ᵐ[μ] fun x => operator (w x) (ξ x))
    (n : ℕ) (hn : 0 < n) (k : ℤ) (a : ℂ) :
    vectorTrace (Lp.const 2 μ (lp.single 2 k a)) (T ^ n) = 0 := by
  unfold vectorTrace
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [InvariantProjection.FieldPowerBounds.ae_pow_apply T
    (fun x => operator (w x)) hT n (Lp.const 2 μ (lp.single 2 k a)),
    Lp.coeFn_const 2 μ (lp.single 2 k a : Hilbert)] with x hpow hconst
  rw [hpow, hconst]
  exact inner_single_operator_pow_eq_zero (w x) n hn k a

end Invariant233.WeightedShift

namespace Invariant233.ProductModel

theorem shift_mul_multiplier_on_vector_ae (θ : ℕ → ℝ) (g : Base → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (ξ : Hilbert) :
    (shiftOperator * multiplier θ g C hC hg hb) ξ =ᵐ[baseMeasure]
      fun x => WeightedShift.operator (multiplierField θ g C hb x) (ξ x) := by
  have hm : multiplier θ g C hC hg hb ξ =ᵐ[baseMeasure]
      fun x => WeightedShift.diagonal (multiplierField θ g C hb x) (ξ x) := by
    unfold multiplier WeightedShift.fieldDiagonal WeightedShift.fieldDiagonalLinear
    exact WeightedShift.fieldDiagonalVec_ae (multiplierField θ g C hb) C hC
      (fun _x => lp.norm_le_of_forall_le hC (fun _k => hb _))
      (fun k => (hg.comp (Measurable.of_eval
        (fun i => (measurable_pi_apply i).add_const _))).aestronglyMeasurable) ξ
  filter_upwards [
    (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap.coeFn_compLpL
      (multiplier θ g C hC hg hb ξ), hm] with x hs hm
  change shiftOperator (multiplier θ g C hC hg hb ξ) x = _
  rw [shiftOperator, hs, hm]
  rfl

theorem vectorTrace_shift_mul_multiplier_pow_eq_zero (θ : ℕ → ℝ) (g : Base → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C)
    (n : ℕ) (hn : 0 < n) :
    vectorTrace traceVector ((shiftOperator * multiplier θ g C hC hg hb) ^ n) = 0 :=
  WeightedShift.vectorTrace_const_pow_eq_zero _ _
    (shift_mul_multiplier_on_vector_ae θ g C hC hg hb) n hn 0 1

theorem vectorTrace_weightedOperator_pow_eq_zero (θ c : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) :
    vectorTrace traceVector (weightedOperator θ c ^ n) = 0 := by
  unfold weightedOperator
  exact vectorTrace_shift_mul_multiplier_pow_eq_zero θ _ _ _ _ _ n hn

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_InvariantConullCore
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233

theorem exists_invariant_conull_subset
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    {s : Set X} (hs : MeasurableSet s) (hfull : ∀ᵐ x ∂μ, x ∈ s) :
    ∃ t : Set X, MeasurableSet t ∧ t ⊆ s ∧
      (∀ᵐ x ∂μ, x ∈ t) ∧ ∀ k, σ k ⁻¹' t = t := by
  let t : Set X := ⋂ k : ℤ, σ k ⁻¹' s
  have ht_mem : ∀ x, x ∈ t ↔ ∀ k, σ k x ∈ s := by
    intro x
    simp only [t, mem_iInter, mem_preimage]
  refine ⟨t, MeasurableSet.iInter (fun k ↦ hs.preimage (hmp k).measurable), ?_, ?_, ?_⟩
  · intro x hx
    simpa only [hzero] using (ht_mem x).mp hx 0
  · have h : ∀ᵐ x ∂μ, ∀ k : ℤ, σ k x ∈ s :=
      ae_all_iff.mpr (fun k ↦ (hmp k).quasiMeasurePreserving.ae hfull)
    exact h.mono fun x hx ↦ (ht_mem x).mpr hx
  · intro k
    ext x
    change σ k x ∈ t ↔ x ∈ t
    rw [ht_mem, ht_mem]
    constructor
    · intro hx n
      have h := hx (n - k)
      rw [← hadd] at h
      rw [← add_sub_assoc, add_comm k n, add_sub_cancel_right] at h
      exact h
    · intro hx n
      rw [← hadd]
      exact hx (k + n)

theorem exists_invariant_conull_property
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : X → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, P x) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨u, hsub, hu, hnull⟩ :=
    exists_measurable_superset_of_null (ae_iff.mp hP)
  have hfull : ∀ᵐ x ∂μ, x ∈ uᶜ := by
    rw [ae_iff]
    simpa using hnull
  obtain ⟨t, ht, htu, htf, hinv⟩ :=
    exists_invariant_conull_subset σ hzero hadd hmp hu.compl hfull
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx
  by_contra hbad
  exact htu hx (hsub hbad)

theorem exists_invariant_conull_forall
    {X I : Type*} [MeasurableSpace X] [Countable I] {μ : Measure X}
    (σ : ℤ → X → X)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ k n x, σ (k + n) x = σ n (σ k x))
    (hmp : ∀ k, MeasurePreserving (σ k) μ μ)
    (P : I → X → Prop) (hP : ∀ i, ∀ᵐ x ∂μ, P i x) :
    ∃ t : Set X, MeasurableSet t ∧ (∀ᵐ x ∂μ, x ∈ t) ∧
      (∀ x ∈ t, ∀ k i, P i (σ k x)) ∧ ∀ k, σ k ⁻¹' t = t := by
  obtain ⟨t, ht, htf, hprop, hinv⟩ :=
    exists_invariant_conull_property σ hzero hadd hmp
      (fun x ↦ ∀ i, P i x) (ae_all_iff.mpr hP)
  refine ⟨t, ht, htf, ?_, hinv⟩
  intro x hx k i
  apply hprop (σ k x) _ i
  change x ∈ σ k ⁻¹' t
  rw [hinv]
  exact hx

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrictlyPositiveNormalization
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra
namespace Invariant233

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

theorem norm_one_sub_normalization_lt_one {a : A} (ha : IsStrictlyPositive a) :
    ‖1 - (‖a‖ + 1)⁻¹ • a‖ < 1 := by
  have hden : 0 < ‖a‖ + 1 := by positivity
  have he : cfc (fun x : ℝ => 1 - (‖a‖ + 1)⁻¹ * x) a =
      1 - (‖a‖ + 1)⁻¹ • a := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => (‖a‖ + 1)⁻¹ * x) a
      (by fun_prop) (by fun_prop), cfc_const 1 a ha.isSelfAdjoint,
      cfc_const_mul_id _ a ha.isSelfAdjoint]
    simp
  rw [← he]
  apply norm_cfc_lt zero_lt_one
  intro x hx
  have hxpos : 0 < x := ha.spectrum_pos hx
  have hxle : x ≤ ‖a‖ :=
    (Real.le_norm_self x).trans (IsometricContinuousFunctionalCalculus.norm_spectrum_le a hx ha.isSelfAdjoint)
  have hlo : 0 < (‖a‖ + 1)⁻¹ * x := mul_pos (inv_pos.mpr hden) hxpos
  have hhi : (‖a‖ + 1)⁻¹ * x < 1 := by
    rw [mul_comm, ← div_eq_mul_inv]
    exact (div_lt_one hden).mpr (lt_of_le_of_lt hxle (lt_add_one _))
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith

theorem exists_pos_norm_one_sub_smul_lt_one {a : A} (ha : IsStrictlyPositive a) :
    ∃ c : ℝ, 0 < c ∧ ‖1 - c • a‖ < 1 :=
  ⟨(‖a‖ + 1)⁻¹, by positivity, norm_one_sub_normalization_lt_one ha⟩

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TruncatedLogIntegral
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem lintegral_cost_eq_iSup_truncations (g : X → ℝ) (hm : Measurable g) :
    (∫⁻ x, ENNReal.ofReal (g x) ∂μ) =
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ := by
  have hsup (x : X) :
      (⨆ n : ℕ, ENNReal.ofReal (min (g x) (n : ℝ))) = ENNReal.ofReal (g x) := by
    apply le_antisymm
    · exact iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)
    · obtain ⟨n, hn⟩ := exists_nat_gt (g x)
      exact le_iSup_of_le n (by rw [min_eq_left hn.le])
  rw [← lintegral_iSup]
  · exact lintegral_congr (fun x => (hsup x).symm)
  · intro n
    exact (hm.min measurable_const).ennreal_ofReal
  · intro n m hnm x
    exact ENNReal.ofReal_le_ofReal (min_le_min_left _ (by exact_mod_cast hnm))

theorem integrable_min_nat_cost [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x) (n : ℕ) :
    Integrable (fun x => min (g x) (n : ℝ)) μ := by
  refine (integrable_const (μ := μ) (n : ℝ)).mono'
    (hm.min measurable_const).aestronglyMeasurable ?_
  exact ae_of_all μ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hg x) (Nat.cast_nonneg n))]
    exact min_le_right _ _

theorem exists_integral_truncation_gt [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) (A : ℝ) :
    ∃ n : ℕ, A < ∫ x, min (g x) (n : ℝ) ∂μ := by
  have hs : (⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ) = ∞ := by
    rw [← lintegral_cost_eq_iSup_truncations g hm, hinf]
  have ht : ENNReal.ofReal A <
      ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (g x) (n : ℝ)) ∂μ := by
    rw [hs]
    exact ENNReal.ofReal_lt_top
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp ht
  refine ⟨n, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_min_nat_cost g hm hg n)
    (ae_of_all μ fun x => le_min (hg x) (Nat.cast_nonneg n))] at hn
  exact (ENNReal.ofReal_lt_ofReal_iff'.mp hn).1

theorem log_max_exp_neg (g M : ℝ) :
    Real.log (max (Real.exp (-g)) (Real.exp (-M))) = -min g M := by
  rcases le_total g M with h | h
  · rw [max_eq_left (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_left h]
  · rw [max_eq_right (Real.exp_le_exp.mpr (neg_le_neg h)), Real.log_exp, min_eq_right h]

theorem integral_truncated_log_eq_neg_cost
    (f g : X → ℝ) (hfg : f =ᵐ[μ] fun x => Real.exp (-g x)) (M : ℝ) :
    (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) =
      -(∫ x, min (g x) M ∂μ) := by
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx, log_max_exp_neg]

theorem tendsto_integral_truncations_atTop [IsFiniteMeasure μ]
    (g : X → ℝ) (hm : Measurable g) (hg : ∀ x, 0 ≤ g x)
    (hinf : (∫⁻ x, ENNReal.ofReal (g x) ∂μ) = ∞) :
    Tendsto (fun n : ℕ => ∫ x, min (g x) (n : ℝ) ∂μ) atTop atTop := by
  apply tendsto_atTop.2
  intro A
  obtain ⟨n, hn⟩ := exists_integral_truncation_gt g hm hg hinf A
  filter_upwards [eventually_ge_atTop n] with m hnm
  refine hn.le.trans (integral_mono (integrable_min_nat_cost g hm hg n)
    (integrable_min_nat_cost g hm hg m) ?_)
  intro x
  exact min_le_min (le_refl (g x)) (Nat.cast_le.mpr hnm)

theorem tendsto_truncated_log_integrals_atBot [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) :
    Tendsto (fun n : ℕ => ∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ)
      atTop atBot := by
  have hfg : f =ᵐ[μ] fun x => Real.exp (-(-Real.log (f x))) := by
    filter_upwards [hpos] with x hx
    simp [Real.exp_log hx]
  have h := tendsto_neg_atTop_atBot.comp
    (tendsto_integral_truncations_atTop (fun x => -Real.log (f x)) hm.log.neg
      (fun x => neg_nonneg.mpr (Real.log_nonpos (hf0 x) (hf1 x))) hinf)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  exact integral_truncated_log_eq_neg_cost f (fun x => -Real.log (f x)) hfg (n : ℝ)

theorem exists_pos_truncated_log_integral_lt [IsFiniteMeasure μ]
    (f : X → ℝ) (hm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x)
    (hinf : (∫⁻ x, ENNReal.ofReal (-Real.log (f x)) ∂μ) = ∞) (a : ℝ) :
    ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) < -2 * a := by
  have hlim := tendsto_truncated_log_integrals_atBot f hm hf0 hf1 hpos hinf
  have hneg : ∀ᶠ n : ℕ in atTop,
      (∫ x, Real.log (max (f x) (Real.exp (-(n : ℝ)))) ∂μ) < -2 * a :=
    hlim.eventually (eventually_lt_atBot (-2 * a))
  obtain ⟨n, hn, hnint⟩ := ((eventually_gt_atTop (0 : ℕ)).and hneg).exists
  exact ⟨n, Nat.cast_pos.mpr hn, hnint⟩

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_CFCLogSeries
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped CStarAlgebra
namespace Invariant233
namespace CFCLogSeries

section Normed
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

omit [CompleteSpace A] in
lemma norm_term_le (a : A) (n : ℕ) : ‖term a n‖ ≤ ‖a‖ ^ (n + 1) := by
  have hn : (1 : ℝ) ≤ n + 1 := by exact le_add_of_nonneg_left (Nat.cast_nonneg n)
  have hi : (n + 1 : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hn
  rw [term, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (norm_pow_le' _ (by omega)) (by positivity)).trans
    (mul_le_of_le_one_left (by positivity) hi)

lemma summable_term {a : A} (ha : ‖a‖ < 1) : Summable (term a) := by
  apply ((summable_nat_add_iff 1).mpr
    (summable_geometric_of_lt_one (norm_nonneg a) ha)).of_norm_bounded
  exact norm_term_le a

end Normed

section CStar
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

private lemma spectrum_abs_lt_one {a : A} (ha : ‖a‖ < 1)
    {x : ℝ} (hx : x ∈ spectrum ℝ a) : |x| < 1 :=
  (spectrum.norm_le_norm_of_mem hx).trans_lt ha

theorem hasSum_neg_log_one_sub {a : A} (hsa : IsSelfAdjoint a) (ha : ‖a‖ < 1) :
    HasSum (term a) (-CFC.log (1 - a)) := by
  let f : C(spectrum ℝ a, ℝ) := (ContinuousMap.id ℝ).restrict (spectrum ℝ a)
  have hf : ‖f‖ ≤ ‖a‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg a)).mpr
    intro x
    exact spectrum.norm_le_norm_of_mem x.property
  have hsum : Summable (term f) := summable_term (hf.trans_lt ha)
  have hc : ContinuousOn (fun x : ℝ => -Real.log (1 - x)) (spectrum ℝ a) := by
    apply ContinuousOn.neg
    apply Real.continuousOn_log.comp (continuous_const.sub continuous_id).continuousOn
    intro x hx
    exact ne_of_gt (sub_pos.mpr ((le_abs_self x).trans_lt (spectrum_abs_lt_one ha hx)))
  let g : C(spectrum ℝ a, ℝ) := ⟨_, hc.domRestrict⟩
  have heq : (∑' n, term f n) = g := by
    ext x
    rw [← ContinuousMap.tsum_apply hsum x]
    simpa [term, f, g, div_eq_mul_inv, mul_comm] using
      (Real.hasSum_pow_div_log_of_abs_lt_one
        (spectrum_abs_lt_one ha x.property)).tsum_eq
  have hmap := (cfcL hsa).hasSum (heq ▸ hsum.hasSum)
  have hid : cfcHom hsa f = a := cfcHom_id hsa
  have hterm : ∀ n, cfcL hsa (term f n) = term a n := by
    intro n
    simp only [term, cfcL_apply, map_smul, map_pow, hid]
  have hg : cfcL hsa g = -CFC.log (1 - a) := by
    change cfcHom hsa g = _
    rw [← cfc_apply (fun x : ℝ => -Real.log (1-x)) a hsa hc]
    rw [cfc_neg]
    change -cfc (fun x : ℝ => Real.log (1-x)) a = _
    have hlog : ContinuousOn Real.log ((fun x : ℝ => 1-x) '' spectrum ℝ a) := by
      apply Real.continuousOn_log.mono
      rintro y ⟨x, hx, rfl⟩
      exact ne_of_gt (sub_pos.mpr ((le_abs_self x).trans_lt (spectrum_abs_lt_one ha hx)))
    rw [cfc_comp' Real.log (fun x : ℝ => 1-x) a hlog]
    have hsub : cfc (fun x : ℝ => 1-x) a = 1-a := by
      rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) a,
        cfc_const_one ℝ a hsa, cfc_id' ℝ a hsa]
    rw [hsub]
    rfl
  simpa only [hterm, hg] using hmap

theorem TracialState_hasSum_log (τ : TracialState A) {a : A}
    (hsa : IsSelfAdjoint a) (ha : ‖a‖ < 1) :
    HasSum (fun n => τ (term a n)) (-τ (CFC.log (1-a))) := by
  simpa only [map_neg] using τ.toContinuousLinearMap.hasSum
    (hasSum_neg_log_one_sub hsa ha)

end CStar
end CFCLogSeries
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_TracialLogDerivative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped Topology CStarAlgebra
namespace Invariant233
namespace CFCLogSeries
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

omit [Nontrivial A] in
lemma trace_pow_derivative_sum (τ : TracialState A) (a b : A) (n : ℕ) :
    τ (∑ i ∈ Finset.range (n+1), a ^ (n-i) * b * a ^ i) =
      (n+1) • τ (a ^ n * b) := by
  rw [map_sum]
  have hterm : ∀ i ∈ Finset.range (n+1),
      τ (a ^ (n-i) * b * a ^ i) = τ (a ^ n * b) := by
    intro i hi
    have hin : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    rw [τ.tracial (a ^ (n-i) * b) (a ^ i), ← mul_assoc, ← pow_add,
      Nat.add_sub_of_le hin]
  calc
    (∑ i ∈ Finset.range (n+1), τ.toContinuousLinearMap (a ^ (n-i) * b * a ^ i)) =
        ∑ _i ∈ Finset.range (n+1), τ (a ^ n * b) := Finset.sum_congr rfl hterm
    _ = _ := by simp

omit [Nontrivial A] in

theorem hasDerivAt_trace_term (τ : TracialState A) {f : ℝ → A} {f' : A} {x : ℝ}
    (hf : HasDerivAt f f' x) (n : ℕ) :
    HasDerivAt (fun t => τ (term (f t) n)) (τ (f x ^ n * f')) x := by
  let L := τ.toContinuousLinearMap.restrictScalars ℝ
  have hd := L.hasFDerivAt.comp_hasDerivAt x
    ((hf.fun_pow' (n+1)).const_smul ((n+1 : ℝ)⁻¹))
  have hvalue : L (((n+1 : ℝ)⁻¹) •
      (∑ i ∈ Finset.range (n+1), f x ^ (n-i) * f' * f x ^ i)) =
      τ (f x ^ n * f') := by
    rw [map_smul]
    change ((n+1 : ℝ)⁻¹) • τ (∑ i ∈ Finset.range (n+1),
      f x ^ (n-i) * f' * f x ^ i) = _
    rw [trace_pow_derivative_sum, ← Nat.cast_smul_eq_nsmul ℝ (n+1), smul_smul]
    simp only [Nat.cast_add, Nat.cast_one,
      inv_mul_cancel₀ (show (n+1 : ℝ) ≠ 0 by positivity), one_smul]
  change HasDerivAt (fun t => τ (term (f t) n))
    (L (((n+1 : ℝ)⁻¹) • (∑ i ∈ Finset.range (n+1),
      f x ^ (n-i) * f' * f x ^ i))) x at hd
  exact hd.congr_deriv hvalue

theorem hasDerivAt_trace_log_one_sub (τ : TracialState A)
    {f f' : ℝ → A} {s : Set ℝ} (hs : IsOpen s) (hsc : IsPreconnected s)
    {r C : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (_hC : 0 ≤ C)
    (hsa : ∀ y ∈ s, IsSelfAdjoint (f y))
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y)
    (hbound : ∀ y ∈ s, ‖f y‖ ≤ r) (hdbound : ∀ y ∈ s, ‖f' y‖ ≤ C)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => τ (CFC.log (1-f y)))
      (-τ (Ring.inverse (1-f x) * f' x)) x := by
  have hu : Summable (fun n : ℕ => ‖τ.toContinuousLinearMap‖ * C * r^n) :=
    (summable_geometric_of_lt_one hr0 hr).mul_left _
  have hterms : ∀ n y, y ∈ s →
      HasDerivAt (fun t => τ (term (f t) n)) (τ (f y ^ n * f' y)) y :=
    fun n y hy => hasDerivAt_trace_term τ (hf y hy) n
  have hb : ∀ n y, y ∈ s →
      ‖τ (f y ^ n * f' y)‖ ≤ ‖τ.toContinuousLinearMap‖ * C * r^n := by
    intro n y hy
    calc
      ‖τ (f y ^ n * f' y)‖ ≤
          ‖τ.toContinuousLinearMap‖ * ‖f y ^ n * f' y‖ :=
        τ.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖τ.toContinuousLinearMap‖ * (‖f y ^ n‖ * ‖f' y‖) := by
        gcongr
        exact norm_mul_le _ _
      _ ≤ ‖τ.toContinuousLinearMap‖ * (r^n * C) := by
        gcongr
        · exact (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) (hbound y hy) n)
        · exact hdbound y hy
      _ = _ := by ring
  have hs0 : Summable (fun n => τ (term (f x) n)) :=
    (TracialState_hasSum_log τ (hsa x hx) ((hbound x hx).trans_lt hr)).summable
  have hd := hasDerivAt_tsum_of_isPreconnected hu hs hsc hterms hb hx hs0 hx
  have hgeom : HasSum (fun n : ℕ => τ (f x ^ n * f' x))
      (τ (Ring.inverse (1-f x) * f' x)) :=
    τ.toContinuousLinearMap.hasSum
      ((hasSum_geom_series_inverse (f x) ((hbound x hx).trans_lt hr)).mul_right (f' x))
  have heq : (fun y => τ (CFC.log (1-f y))) =ᶠ[𝓝 x]
      (fun y => -(∑' n, τ (term (f y) n))) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [(TracialState_hasSum_log τ (hsa y hy) ((hbound y hy).trans_lt hr)).tsum_eq,
      neg_neg]
  have hout := hd.neg.congr_of_eventuallyEq heq
  simpa only [hgeom.tsum_eq] using hout

variable [PartialOrder A] [StarOrderedRing A]

theorem hasDerivAt_trace_log_of_scaled_ball (τ : TracialState A)
    {f f' : ℝ → A} {s : Set ℝ} (hs : IsOpen s) (hsc : IsPreconnected s)
    {c r C : ℝ} (hc : 0 < c) (hr0 : 0 ≤ r) (hr : r < 1) (hC : 0 ≤ C)
    (hpos : ∀ y ∈ s, IsStrictlyPositive (f y))
    (hf : ∀ y ∈ s, HasDerivAt f (f' y) y)
    (hbound : ∀ y ∈ s, ‖1-c • f y‖ ≤ r) (hdbound : ∀ y ∈ s, ‖f' y‖ ≤ C)
    {x : ℝ} (hx : x ∈ s) :
    HasDerivAt (fun y => τ (CFC.log (f y)))
      (τ (Ring.inverse (f x) * f' x)) x := by
  have hd := hasDerivAt_trace_log_one_sub τ hs hsc hr0 hr
    (mul_nonneg hc.le hC)
    (f := fun y => 1-c • f y) (f' := fun y => -(c • f' y))
    (fun y hy => (show IsSelfAdjoint (1 : A) by simp).sub ((IsSelfAdjoint.all c).smul (hpos y hy).isSelfAdjoint))
    (fun y hy => ((hf y hy).const_smul c).const_sub 1)
    hbound (fun y hy => by
      simpa only [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hc] using
        mul_le_mul_of_nonneg_left (hdbound y hy) hc.le) hx
  have hinv : Ring.inverse (c • f x) * (c • f' x) =
      Ring.inverse (f x) * f' x := by
    apply (Ring.inverse_mul_eq_iff_eq_mul (c • f x) (c • f' x)
      (Ring.inverse (f x) * f' x) ((hpos x hx).smul hc).isUnit).mpr
    rw [smul_mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ (hpos x hx).isUnit,
      one_mul]
  have hd' : HasDerivAt (fun y => τ (CFC.log (c • f y)))
      (τ (Ring.inverse (f x) * f' x)) x := by
    simpa only [sub_sub_cancel, mul_neg, map_neg, neg_neg, hinv] using hd
  have heq : (fun y => τ (CFC.log (f y))) =ᶠ[𝓝 x]
      (fun y => τ (CFC.log (c • f y)) - τ (algebraMap ℝ A (Real.log c))) := by
    filter_upwards [hs.mem_nhds hx] with y hy
    rw [CFC.log_smul' (f y) hc (hpos y hy), map_add, add_sub_cancel_left]
  exact (hd'.sub_const (τ (algebraMap ℝ A (Real.log c)))).congr_of_eventuallyEq heq

theorem hasDerivAt_trace_log_of_normalization (τ : TracialState A)
    {f f' : ℝ → A} (hpos : ∀ y, IsStrictlyPositive (f y))
    (hf : ∀ y, HasDerivAt f (f' y) y) {x : ℝ} (hcf' : ContinuousAt f' x)
    (hscale : ∃ c : ℝ, 0 < c ∧ ‖1-c • f x‖ < 1) :
    HasDerivAt (fun y => τ (CFC.log (f y)))
      (τ (Ring.inverse (f x) * f' x)) x := by
  obtain ⟨c, hc, hcball⟩ := hscale
  let r := (‖1-c • f x‖ + 1) / 2
  have hr0 : 0 ≤ r := by dsimp [r] <;> positivity
  have hr : r < 1 := by dsimp [r] <;> linarith
  have hrx : ‖1-c • f x‖ < r := by dsimp [r] <;> linarith
  have hcont : ContinuousAt (fun y => ‖1-c • f y‖) x :=
    (continuousAt_const.sub ((hf x).continuousAt.const_smul c)).norm
  have he1 : ∀ᶠ y in 𝓝 x, ‖1-c • f y‖ < r :=
    hcont.eventually_lt_const hrx
  have he2 : ∀ᶠ y in 𝓝 x, ‖f' y‖ < ‖f' x‖ + 1 :=
    hcf'.norm.eventually_lt_const (by linarith)
  obtain ⟨l, u, hxu, hlu⟩ := (he1.and he2).exists_Ioo_subset
  exact hasDerivAt_trace_log_of_scaled_ball τ isOpen_Ioo (convex_Ioo l u).isPreconnected
    hc hr0 hr (by positivity : 0 ≤ ‖f' x‖+1)
    (fun y _ => hpos y) (fun y _ => hf y)
    (fun y hy => (hlu hy).1.le) (fun y hy => (hlu hy).2.le) hxu

end CFCLogSeries
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_TracialNormSquareDerivative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233
namespace TracialState
variable {A : Type*} [CStarAlgebra A]

theorem inverse_normSquare_first_term (τ : TracialState A) (a b : A)
    (ha : IsUnit a) :
    τ ((Ring.inverse a * star (Ring.inverse a)) * (star b * a)) =
      star (τ (Ring.inverse a * b)) := by
  calc
    τ ((Ring.inverse a * star (Ring.inverse a)) * (star b * a)) =
        τ (((Ring.inverse a * star (Ring.inverse a)) * star b) * a) := by
          simp only [mul_assoc]
    _ = τ (a * ((Ring.inverse a * star (Ring.inverse a)) * star b)) :=
      τ.tracial _ _
    _ = τ ((a * Ring.inverse a) * (star (Ring.inverse a) * star b)) := by
      simp only [mul_assoc]
    _ = τ (star (Ring.inverse a) * star b) := by
      rw [Ring.mul_inverse_cancel a ha, one_mul]
    _ = star (τ (b * Ring.inverse a)) := by rw [← star_mul, τ.map_star]
    _ = star (τ (Ring.inverse a * b)) := by rw [τ.tracial b (Ring.inverse a)]

theorem inverse_normSquare_second_term (a b : A) (ha : IsUnit a) :
    (Ring.inverse a * star (Ring.inverse a)) * (star a * b) =
      Ring.inverse a * b := by
  have hc : star (Ring.inverse a) * star a = 1 := by
    rw [← star_mul, Ring.mul_inverse_cancel a ha, star_one]
  calc
    (Ring.inverse a * star (Ring.inverse a)) * (star a * b) =
        Ring.inverse a * ((star (Ring.inverse a) * star a) * b) := by
          simp only [mul_assoc]
    _ = Ring.inverse a * b := by rw [hc, one_mul]

theorem re_inverse_normSquare_differential (τ : TracialState A) (a b : A)
    (ha : IsUnit a) :
    (τ (Ring.inverse (star a * a) * (star b * a + star a * b))).re =
      2 * (τ (Ring.inverse a * b)).re := by
  rw [Ring.inverse_mul (Or.inr ha), Ring.inverse_star, mul_add, map_add,
    τ.inverse_normSquare_first_term a b ha, inverse_normSquare_second_term a b ha]
  simp [Complex.add_re, two_mul]

theorem hasDerivAt_normSquare {f : ℝ → A} {f' : A} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => star (f s) * f s)
      (star f' * f t + star (f t) * f') t := by
  exact hf.star.mul hf

end TracialState
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_TracialLogNormSquare
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233
namespace CFCLogSeries
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable [PartialOrder A] [StarOrderedRing A]

theorem hasDerivAt_re_trace_log_normSquare_of_normalization (τ : TracialState A)
    {f f' : ℝ → A} (hunit : ∀ y, IsUnit (f y))
    (hf : ∀ y, HasDerivAt f (f' y) y) {x : ℝ} (hcf' : ContinuousAt f' x)
    (hscale : ∃ c : ℝ, 0 < c ∧ ‖1-c • (star (f x) * f x)‖ < 1) :
    HasDerivAt (fun y => (τ (CFC.log (star (f y) * f y))).re)
      (2 * (τ (Ring.inverse (f x) * f' x)).re) x := by
  have hp : ∀ y, IsStrictlyPositive (star (f y) * f y) :=
    fun y => ⟨star_mul_self_nonneg _, (hunit y).star.mul (hunit y)⟩
  have hq' : ContinuousAt (fun y => star (f' y) * f y + star (f y) * f' y) x :=
    (hcf'.star.mul (hf x).continuousAt).add ((hf x).continuousAt.star.mul hcf')
  have hlog := hasDerivAt_trace_log_of_normalization τ hp
    (fun y => TracialState.hasDerivAt_normSquare (hf y)) hq' hscale
  have hre := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x hlog
  change HasDerivAt (fun y => (τ (CFC.log (star (f y) * f y))).re)
    (τ (Ring.inverse (star (f x) * f x) *
      (star (f' x) * f x + star (f x) * f' x))).re x at hre
  exact hre.congr_deriv (τ.re_inverse_normSquare_differential (f x) (f' x) (hunit x))

theorem hasDerivAt_re_trace_log_normSquare (τ : TracialState A)
    {f f' : ℝ → A} (hunit : ∀ y, IsUnit (f y))
    (hf : ∀ y, HasDerivAt f (f' y) y) {x : ℝ} (hcf' : ContinuousAt f' x) :
    HasDerivAt (fun y => (τ (CFC.log (star (f y) * f y))).re)
      (2 * (τ (Ring.inverse (f x) * f' x)).re) x :=
  hasDerivAt_re_trace_log_normSquare_of_normalization τ hunit hf hcf'
    (exists_pos_norm_one_sub_smul_lt_one
      ⟨star_mul_self_nonneg _, (hunit x).star.mul (hunit x)⟩)

end CFCLogSeries
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRepresentative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem measurePreserving_productRepresentative {ι : Type*} (i : ι) :
    MeasurePreserving
      (fun x : ι → UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩
  exact measurePreserving_circleRepresentative.comp
    (measurePreserving_eval_infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)) i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.CocycleSupport

theorem uniform_floor_ne_zero_le (t : ℝ) :
    (volume.restrict (Ico (0 : ℝ) 1)) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ≤
      ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  rw [Measure.restrict_apply hm]
  rcases le_or_gt 0 t with ht | ht
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico (1 - t) 1) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨?_, hx1⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, abs_of_nonneg ht]
        congr 1
        ring
  · calc
      volume ({x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} ∩ Ico 0 1) ≤
          volume (Ico 0 (-t)) := by
        apply measure_mono
        rintro x ⟨hx, hx0, hx1⟩
        refine ⟨hx0, ?_⟩
        by_contra h
        apply hx
        apply Int.floor_eq_zero_iff.mpr
        constructor <;> linarith
      _ = ENNReal.ofReal |t| := by
        rw [Real.volume_Ico, sub_zero, abs_of_neg ht]

theorem ae_finite_support_of_tsum_ne_top {Ω ι A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Zero A]
    (μ : Measure Ω) (a : ι → Ω → A)
    (h : (∑' i, μ {x | a i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, (Function.support (fun i => a i x)).Finite := by
  exact ae_finite_setOfPred_mem h

theorem ae_all_finite_support_of_tsum_ne_top {Ω ι K A : Type*}
    [MeasurableSpace Ω] [Countable ι] [Countable K] [Zero A]
    (μ : Measure Ω) (a : K → ι → Ω → A)
    (h : ∀ k, (∑' i, μ {x | a k i x ≠ 0}) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ k, (Function.support (fun i => a k i x)).Finite := by
  rw [ae_all_iff]
  intro k
  exact ae_finite_support_of_tsum_ne_top μ (a k) (h k)

theorem measure_floor_ne_zero_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (u : Ω → ℝ) (hu : Measurable u)
    (hlaw : μ.map u = volume.restrict (Ico (0 : ℝ) 1)) (t : ℝ) :
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} ≤ ENNReal.ofReal |t| := by
  have hm : MeasurableSet {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
    ((measurable_id.add_const t).floor (measurableSet_singleton 0)).compl
  calc
    μ {x | ⌊u x + t⌋ ≠ (0 : ℤ)} =
        (μ.map u) {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} :=
      (Measure.map_apply hu hm).symm
    _ = (volume.restrict (Ico (0 : ℝ) 1))
        {x : ℝ | ⌊x + t⌋ ≠ (0 : ℤ)} := by rw [hlaw]
    _ ≤ ENNReal.ofReal |t| := uniform_floor_ne_zero_le t

theorem ae_all_int_finite_floor_support {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (u : ι → Ω → ℝ) (hu : ∀ i, Measurable (u i))
    (hlaw : ∀ i, μ.map (u i) = volume.restrict (Ico (0 : ℝ) 1))
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => (⌊u i x + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  apply ae_all_finite_support_of_tsum_ne_top
  intro k
  apply ne_top_of_le_ne_top ((hθ.mul_left |(k : ℝ)|).tsum_ofReal_ne_top)
  apply ENNReal.tsum_le_tsum
  intro i
  simpa only [abs_mul, abs_of_nonneg (hθ0 i)] using
    measure_floor_ne_zero_le μ (u i) (hu i) (hlaw i) ((k : ℝ) * θ i)

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set

namespace Invariant233.CocycleSupport

theorem ae_product_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (θ : ι → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∀ᵐ x ∂(Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))),
      ∀ k : ℤ,
        (Function.support (fun i =>
          (⌊((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ) + (k : ℝ) * θ i⌋ : ℤ))).Finite := by
  exact ae_all_int_finite_floor_support
    (Ω := ι → UnitAddCircle) (ι := ι)
    (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (x i)) : ℝ))
    (fun i => (measurePreserving_productRepresentative i).measurable)
    (fun i => (measurePreserving_productRepresentative i).map_eq)
    θ hθ0 hθ

end Invariant233.CocycleSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FloorCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace FloorCocycle

theorem floor_fract_add (x y : ℝ) :
    ⌊Int.fract x + y⌋ + ⌊x⌋ = ⌊x + y⌋ := by
  rw [Int.fract, sub_add_eq_add_sub, Int.floor_sub_intCast]
  omega

theorem floor_cocycle (u α : ℝ) (v n : ℤ) :
    ⌊u + (v : ℝ) * α⌋ + ⌊Int.fract (u + (v : ℝ) * α) + (n : ℝ) * α⌋ =
      ⌊u + ((v + n : ℤ) : ℝ) * α⌋ := by
  rw [add_comm, floor_fract_add]
  congr 1
  push_cast
  ring

theorem floor_add_eq_indicator {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u < 1) (t : ℝ) :
    ⌊u + t⌋ = ⌊t⌋ + if 1 - Int.fract t ≤ u then 1 else 0 := by
  have hsplit : ⌊u + t⌋ = ⌊u + Int.fract t⌋ + ⌊t⌋ := by
    rw [← Int.floor_add_intCast]
    congr 1
    rw [add_assoc, Int.fract_add_floor]
  rw [hsplit]
  split_ifs with h
  · have hf : ⌊u + Int.fract t⌋ = 1 := by
      apply Int.floor_eq_iff.mpr
      constructor
      · norm_num
        linarith
      · norm_num
        linarith [Int.fract_lt_one t]
    rw [hf]
    omega
  · have hf : ⌊u + Int.fract t⌋ = 0 := by
      apply Int.floor_eq_zero_iff.mpr
      constructor
      · exact add_nonneg hu₀ (Int.fract_nonneg t)
      · linarith
    rw [hf]
    omega

end FloorCocycle
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function

namespace Invariant233.FiniteSupportCocycle

theorem summable_weighted_int {I : Type*} (c : I → ℝ) {a : I → ℤ}
    (ha : HasFiniteSupport a) : Summable (fun i ↦ c i * (a i : ℝ)) := by
  apply summable_of_hasFiniteSupport
  exact HasFiniteSupport.mul_right c (ha.fun_comp (by simp))

theorem exp_tsum_floor_cocycle {I : Type*} (x θ c : I → ℝ) (k n : ℤ)
    (hk : HasFiniteSupport (fun i ↦ ⌊x i + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋)) :
    Real.exp (-(∑' i, c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ))) =
      Real.exp (-(∑' i, c i *
        (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ))) *
      Real.exp (-(∑' i, c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ))) := by
  have hcoord (i : I) :
      c i * (⌊x i + ((k + n : ℤ) : ℝ) * θ i⌋ : ℝ) =
        c i * (⌊x i + (k : ℝ) * θ i⌋ : ℝ) +
        c i * (⌊Int.fract (x i + (k : ℝ) * θ i) + (n : ℝ) * θ i⌋ : ℝ) := by
    rw [← FloorCocycle.floor_cocycle]
    push_cast
    ring
  rw [tsum_congr hcoord,
    (summable_weighted_int c hk).tsum_add (summable_weighted_int c hn),
    neg_add, Real.exp_add, mul_comm]

theorem exp_tsum_floor_zero {I : Type*} (x c : I → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1) :
    Real.exp (-(∑' i, c i * (⌊x i⌋ : ℝ))) = 1 := by
  have hf (i : I) : ⌊x i⌋ = 0 := Int.floor_eq_zero_iff.mpr (hx i)
  simp [hf]

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.ProductCocycle

theorem representative_mem_Ico (x : UnitAddCircle) :
    representative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [representative, zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem representative_add (x : UnitAddCircle) (t : ℝ) :
    representative (x + (t : UnitAddCircle)) = Int.fract (representative x + t) := by
  have hx : x + (t : UnitAddCircle) =
      ((representative x + t : ℝ) : UnitAddCircle) := by
    rw [AddCircle.coe_add, coe_representative]
  rw [hx]
  change ((AddCircle.equivIco (1 : ℝ) 0
    ((representative x + t : ℝ) : UnitAddCircle)) : ℝ) = _
  simpa only [div_one, mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) (representative x + t))

theorem representative_rotate {I : Type*} (θ : I → ℝ) (k : ℤ)
    (x : Space I) (i : I) :
    representative (rotate θ k x i) =
      Int.fract (representative (x i) + (k : ℝ) * θ i) :=
  representative_add (x i) ((k : ℝ) * θ i)

theorem cocycleVersion_pos {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) :
    0 < cocycleVersion θ c k x :=
  Real.exp_pos _

@[simp] theorem cocycleVersion_zero {I : Type*} (θ c : I → ℝ) (x : Space I) :
    cocycleVersion θ c 0 x = 1 := by
  simp only [cocycleVersion, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero _ c
    (fun i ↦ representative_mem_Ico (x i))

theorem cocycleVersion_add_of_finite_support {I : Type*}
    (θ c : I → ℝ) (k n : ℤ) (x : Space I)
    (hk : HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
    (hn : HasFiniteSupport
      (fun i ↦ ⌊representative (rotate θ k x i) + (n : ℝ) * θ i⌋)) :
    cocycleVersion θ c (k + n) x =
      cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x := by
  simp only [cocycleVersion, representative_rotate] at hn ⊢
  exact FiniteSupportCocycle.exp_tsum_floor_cocycle _ θ c k n hk hn

theorem exists_invariant_cocycle_core {I : Type*} [Countable I]
    (θ : I → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθ : Summable θ) :
    ∃ s : Set (Space I), MeasurableSet s ∧ (∀ᵐ x ∂haar I, x ∈ s) ∧
      (∀ k : ℤ, rotate θ k ⁻¹' s = s) ∧
      (∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋)) ∧
      (∀ x ∈ s, ∀ (c : I → ℝ) (k n : ℤ),
        cocycleVersion θ c (k + n) x =
          cocycleVersion θ c n (rotate θ k x) * cocycleVersion θ c k x) := by
  have hall : ∀ᵐ x ∂haar I, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) :=
    CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  obtain ⟨s, hs, hfull, hprop, hinv⟩ :=
    Invariant233.exists_invariant_conull_forall (rotate θ) (rotate_zero θ)
      (rotate_add θ) (measurePreserving_rotate θ)
      (fun (k : ℤ) (x : Space I) ↦ HasFiniteSupport
        (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋))
      (ae_all_iff.mp hall)
  have hsupport (x : Space I) (hx : x ∈ s) (k : ℤ) :
      HasFiniteSupport (fun i ↦ ⌊representative (x i) + (k : ℝ) * θ i⌋) := by
    simpa only [rotate_zero] using hprop x hx 0 k
  refine ⟨s, hs, hfull, hinv, hsupport, ?_⟩
  intro x hx c k n
  exact cocycleVersion_add_of_finite_support θ c k n x
    (hsupport x hx k) (hprop x hx k n)

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductWeightBridge
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped ENNReal

namespace Invariant233.ProductModel

theorem cost_summand_nonneg (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base) (i : ℕ) :
    0 ≤ c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) := by
  apply mul_nonneg (hc i)
  have hf : (0 : ℤ) ≤ ⌊circleRepresentative (x i) + θ i⌋ := by
    apply Int.floor_nonneg.mpr
    exact add_nonneg (ProductCocycle.representative_mem_Ico (x i)).1 (hθ i)
  exact_mod_cast hf

theorem logarithmicCost_eq_ofReal_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    logarithmicCost θ c x =
      ENNReal.ofReal (∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ)) := by
  exact (ENNReal.ofReal_tsum_of_nonneg
    (cost_summand_nonneg θ c hθ hc x)
    (FiniteSupportCocycle.summable_weighted_int c hx)).symm

theorem weight_eq_cocycleVersion_of_finite_support (θ c : ℕ → ℝ)
    (hθ : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (x : Base)
    (hx : HasFiniteSupport (fun i ↦ ⌊circleRepresentative (x i) + θ i⌋)) :
    weight θ c x = ProductCocycle.cocycleVersion θ c 1 x := by
  have hnonneg : 0 ≤ ∑' i, c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ) :=
    tsum_nonneg (cost_summand_nonneg θ c hθ hc x)
  unfold weight
  rw [logarithmicCost_eq_ofReal_tsum θ c hθ hc x hx,
    EReal.coe_ennreal_ofReal, max_eq_left hnonneg, ← EReal.coe_neg,
    EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  simp only [ProductCocycle.cocycleVersion, Int.cast_one, one_mul,
    circleRepresentative, ProductCocycle.representative]

theorem negLogCost_weight (θ c : ℕ → ℝ) (x : Base) :
    negLogCost (weight θ c x) = logarithmicCost θ c x :=
  negLogCost_extendedExpNeg _

theorem weight_ae_eq_cocycleVersion (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    weight θ c =ᵐ[baseMeasure] ProductCocycle.cocycleVersion θ c 1 := by
  have hall := CocycleSupport.ae_product_all_int_finite_floor_support θ hθ0 hθ
  filter_upwards [hall] with x hx
  apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc x
  simpa only [HasFiniteSupport, circleRepresentative, Int.cast_one, one_mul] using hx 1

theorem ae_weight_pos (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ) :
    ∀ᵐ x ∂baseMeasure, 0 < weight θ c x := by
  filter_upwards [weight_ae_eq_cocycleVersion θ c hθ0 hc hθ] with x hx
  rw [hx]
  exact ProductCocycle.cocycleVersion_pos θ c 1 x

theorem lintegral_negLogCost_weight (θ c : ℕ → ℝ) :
    (∫⁻ x, negLogCost (weight θ c x) ∂baseMeasure) =
      ∫⁻ x, logarithmicCost θ c x ∂baseMeasure := by
  simp only [negLogCost_weight]

theorem hasNegInfiniteLogIntegral_iff (θ c : ℕ → ℝ) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ c) ↔
      (∫⁻ x, logarithmicCost θ c x ∂baseMeasure) = ∞ := by
  rw [HasNegInfiniteLogIntegral, lintegral_negLogCost_weight]

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductLogIntegral
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel

theorem uniform_floorCost_integral (θ c : ℝ) (hθ : θ ∈ Ico (0 : ℝ) 1)
    (hc : 0 ≤ c) :
    (∫⁻ u : ℝ, ENNReal.ofReal (c * (⌊u + θ⌋ : ℝ))
      ∂(volume.restrict (Ico (0 : ℝ) 1))) = ENNReal.ofReal (c * θ) := by
  classical
  have heq : (fun u : ℝ ↦ ENNReal.ofReal (c * (⌊u + θ⌋ : ℝ))) =ᵐ[
      volume.restrict (Ico (0 : ℝ) 1)]
      (Ici (1 - θ)).indicator (fun _ ↦ ENNReal.ofReal c) := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ico] with u hu
    rw [FloorCocycle.floor_add_eq_indicator hu.1 hu.2,
      Int.floor_eq_zero_iff.mpr hθ, Int.fract_eq_self.mpr hθ, zero_add]
    by_cases h : 1 - θ ≤ u
    · simp [h]
    · simp [h]
  have hinter : Ici (1 - θ) ∩ Ico (0 : ℝ) 1 = Ico (1 - θ) 1 := by
    ext u
    constructor
    · rintro ⟨ha, _, hb⟩
      exact ⟨ha, hb⟩
    · intro hu
      exact ⟨hu.1, by linarith [hu.1, hθ.2], hu.2⟩
  rw [lintegral_congr_ae heq, lintegral_indicator_const measurableSet_Ici,
    Measure.restrict_apply measurableSet_Ici, hinter, Real.volume_Ico]
  rw [show (1 : ℝ) - (1 - θ) = θ by ring, ← ENNReal.ofReal_mul hc]

theorem measurable_cost_summand (θ c : ℕ → ℝ) (i : ℕ) :
    Measurable (fun x : Base ↦
      ENNReal.ofReal (c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ))) := by
  have hrep : Measurable (fun x : Base ↦ circleRepresentative (x i)) :=
    ProductCocycle.measurable_representative.comp (measurable_pi_apply i)
  exact (measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
    ((hrep.add_const (θ i)).floor))).ennreal_ofReal

theorem lintegral_cost_summand (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) (i : ℕ) :
    (∫⁻ x, ENNReal.ofReal (c i * (⌊circleRepresentative (x i) + θ i⌋ : ℝ))
      ∂baseMeasure) = ENNReal.ofReal (c i * θ i) := by
  have hm : Measurable (fun u : ℝ ↦ ENNReal.ofReal (c i * (⌊u + θ i⌋ : ℝ))) :=
    (measurable_const.mul ((measurable_of_countable (fun z : ℤ ↦ (z : ℝ))).comp
      ((measurable_id.add_const (θ i)).floor))).ennreal_ofReal
  calc
    _ = ∫⁻ u : ℝ, ENNReal.ofReal (c i * (⌊u + θ i⌋ : ℝ))
        ∂(volume.restrict (Ico (0 : ℝ) 1)) :=
      (CocycleSupport.measurePreserving_productRepresentative i).lintegral_comp hm
    _ = ENNReal.ofReal (c i * θ i) := uniform_floorCost_integral _ _ (hθ i) (hc i)

theorem lintegral_logarithmicCost (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) :
    (∫⁻ x, logarithmicCost θ c x ∂baseMeasure) =
      ∑' i, ENNReal.ofReal (c i * θ i) := by
  unfold logarithmicCost
  rw [lintegral_tsum (fun i ↦ (measurable_cost_summand θ c i).aemeasurable)]
  exact tsum_congr (lintegral_cost_summand θ c hθ hc)

theorem hasNegInfiniteLogIntegral_iff_tsum (θ c : ℕ → ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i) :
    HasNegInfiniteLogIntegral baseMeasure (weight θ c) ↔
      (∑' i, ENNReal.ofReal (c i * θ i)) = ∞ := by
  rw [hasNegInfiniteLogIntegral_iff, lintegral_logarithmicCost θ c hθ hc]

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal lp Topology

namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)

variable {a C hC ha hm}

theorem fieldShift_ae (m : ℤ) (f : Lp Hilbert 2 μ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f =ᵐ[μ]
      fun x => shift m (f x) :=
  ContinuousLinearMap.coeFn_compLp _ f

theorem fieldShift_add (m n : ℤ) :
    (shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ =
      (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ *
        (shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ := by
  ext f
  filter_upwards [fieldShift_ae (m + n) f,
    fieldShift_ae m ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f),
    fieldShift_ae n f] with x hmn hm hn
  change ((shift (m + n)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x =
    ((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
      ((shift n).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f)) x
  rw [hmn, hm, hn]
  exact congrArg (fun A : Hilbert →L[ℂ] Hilbert => A (f x)) (shift_add m n)

theorem fieldShift_zero :
    (shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ = 1 := by
  ext f
  filter_upwards [fieldShift_ae 0 f] with x hx
  change ((shift 0).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x = f x
  rw [hx]
  change (shift 0).toLinearIsometry.toContinuousLinearMap (f x) = f x
  rw [shift_zero]
  rfl

theorem fieldShift_norm_map (m : ℤ) (f : Lp Hilbert 2 μ) :
    ‖(shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ,
      ‖((shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ f) x‖ = ‖f x‖ := by
    filter_upwards [fieldShift_ae m f] with x hx
    rw [hx, (shift m).norm_map]
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldShift_mem_unitary (m : ℤ) :
    (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ ∈
      unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  let A := (shift m).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  let B := (shift (-m)).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
  have hAB : A * B = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hBA : B * A = 1 := by
    dsimp [A, B]
    rw [← fieldShift_add]
    simpa using (fieldShift_zero (μ := μ))
  have hA : IsUnit A := ⟨⟨A, B, hAB, hBA⟩, rfl⟩
  apply hA.mem_unitary_iff_star_mul_self.mpr
  change ContinuousLinearMap.adjoint A ∘L A = 1
  exact A.norm_map_iff_adjoint_comp_self.mp (fieldShift_norm_map m)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ScalarDeterminantZero
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped Topology ENNReal

namespace Invariant233.ScalarDeterminant

theorem log_sq_add_sq_le {a t : ℝ} (ha : 0 ≤ a) (ht : 0 < t) :
    Real.log (a ^ 2 + t ^ 2) ≤ Real.log 2 + 2 * Real.log (max a t) := by
  have hm : 0 < max a t := ht.trans_le (le_max_right a t)
  have ha2 := pow_le_pow_left₀ ha (le_max_left a t) 2
  have ht2 := pow_le_pow_left₀ ht.le (le_max_right a t) 2
  have hlog : Real.log (a ^ 2 + t ^ 2) ≤ Real.log (2 * (max a t) ^ 2) :=
    Real.log_le_log (by positivity) (by linarith)
  calc
    _ ≤ Real.log (2 * (max a t) ^ 2) := hlog
    _ = _ := by rw [Real.log_mul (by norm_num) (pow_ne_zero _ hm.ne'), Real.log_pow]; norm_num

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integrable_regularized_log {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x => Real.log (f x ^ 2 + ε)) μ := by
  refine (integrable_const (|Real.log ε| + |Real.log (1 + ε)|)).mono'
    ((hf.pow_const 2 |>.add_const ε).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hx := hbound x
  have hlo : Real.log ε ≤ Real.log (f x ^ 2 + ε) :=
    Real.log_le_log hε (le_add_of_nonneg_left (sq_nonneg _))
  have hhi : Real.log (f x ^ 2 + ε) ≤ Real.log (1 + ε) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · have := neg_abs_le (Real.log ε)
    have := abs_nonneg (Real.log (1 + ε))
    linarith
  · have := le_abs_self (Real.log (1 + ε))
    have := abs_nonneg (Real.log ε)
    linarith

theorem integrable_truncated_log {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {M : ℝ} (hM : 0 < M) :
    Integrable (fun x => Real.log (max (f x) (Real.exp (-M)))) μ := by
  refine (integrable_const M).mono'
    ((hf.max measurable_const).log.aestronglyMeasurable) ?_
  filter_upwards [] with x
  have hp : 0 < max (f x) (Real.exp (-M)) :=
    (Real.exp_pos _).trans_le (le_max_right _ _)
  have hlo : -M ≤ Real.log (max (f x) (Real.exp (-M))) := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos (-M)) (le_max_right (f x) (Real.exp (-M)))
  have hhi : Real.log (max (f x) (Real.exp (-M))) ≤ 0 := by
    apply Real.log_nonpos hp.le
    exact max_le (hbound x).2 (Real.exp_le_one_iff.mpr (by linarith))
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨hlo, hhi.trans hM.le⟩

variable [IsProbabilityMeasure μ]

theorem integral_regularized_log_le {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1) {M : ℝ} (hM : 0 < M) :
    (∫ x, Real.log (f x ^ 2 + (Real.exp (-M)) ^ 2) ∂μ) ≤
      Real.log 2 + 2 * ∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ := by
  have hint := integrable_truncated_log (μ := μ) hf hbound hM
  calc
    _ ≤ ∫ x, Real.log 2 + 2 * Real.log (max (f x) (Real.exp (-M))) ∂μ :=
      integral_mono (integrable_regularized_log hf hbound (sq_pos_of_pos (Real.exp_pos _)))
        ((integrable_const _).add (hint.const_mul 2))
        (fun x => log_sq_add_sq_le (hbound x).1 (Real.exp_pos _))
    _ = _ := by
      rw [integral_add (integrable_const _) (hint.const_mul 2), integral_const_mul]
      simp

theorem regularized_determinant_eq_zero {f : X → ℝ} (hf : Measurable f)
    (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (htrunc : ∀ B : ℝ, ∃ M : ℝ, 0 < M ∧
      (∫ x, Real.log (max (f x) (Real.exp (-M))) ∂μ) < B) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) = 0 := by
  apply le_antisymm _ bot_le
  have hlow (n : ℕ) :
      (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) ≤
      ENNReal.ofReal (Real.exp (-(n : ℝ))) := by
    obtain ⟨M, hM, hsmall⟩ := htrunc (-(n : ℝ) - Real.log 2 / 2)
    have hint := integral_regularized_log_le (μ := μ) hf hbound hM
    calc
      _ ≤ ENNReal.ofReal (Real.exp
          ((∫ x, Real.log (f x ^ 2 + (Real.exp (-M)) ^ 2) ∂μ) / 2)) :=
        iInf_le _ (⟨(Real.exp (-M)) ^ 2, sq_pos_of_pos (Real.exp_pos _)⟩ : {r : ℝ // 0 < r})
      _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.mpr
        linarith
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(n : ℝ))))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop)
  exact ge_of_tendsto' hlim hlow


end Invariant233.ScalarDeterminant

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_Spectral
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Invariant233

theorem exp_half_log_eq_sqrt {t : ℝ} (ht : 0 < t) :
    Real.exp (Real.log t / 2) = Real.sqrt t := by
  rw [← Real.log_sqrt ht.le, Real.exp_log (Real.sqrt_pos.mpr ht)]

theorem iInf_sqrt_sq_add_pos (c : ℝ) (hc : 0 ≤ c) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal (Real.sqrt (c ^ 2 + ε.val))) =
      ENNReal.ofReal c := by
  apply le_antisymm
  · have hlim : Tendsto
        (fun n : ℕ => ENNReal.ofReal (Real.sqrt (c ^ 2 + 1 / ((n : ℝ) + 1))))
        atTop (𝓝 (ENNReal.ofReal c)) := by
      have hreal : Tendsto (fun n : ℕ => c ^ 2 + 1 / ((n : ℝ) + 1))
          atTop (𝓝 (c ^ 2)) := by
        simpa using tendsto_const_nhds.add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      simpa [Function.comp_def, Real.sqrt_sq hc] using
        ENNReal.continuous_ofReal.continuousAt.tendsto.comp
          (Real.continuous_sqrt.continuousAt.tendsto.comp hreal)
    apply ge_of_tendsto' hlim
    intro n
    exact iInf_le (fun ε : {r : ℝ // 0 < r} =>
      ENNReal.ofReal (Real.sqrt (c ^ 2 + ε.val))) ⟨1 / ((n : ℝ) + 1), by positivity⟩
  · apply le_iInf
    intro ε
    apply ENNReal.ofReal_le_ofReal
    calc
      c = Real.sqrt (c ^ 2) := (Real.sqrt_sq hc).symm
      _ ≤ Real.sqrt (c ^ 2 + ε.val) := Real.sqrt_le_sqrt (by linarith [ε.property])

theorem logarithmicPotentialDeterminant_dirac (w z : ℂ) :
    logarithmicPotentialDeterminant (Measure.dirac w) z = ENNReal.ofReal ‖w - z‖ := by
  simp only [logarithmicPotentialDeterminant, integral_dirac]
  have h : ∀ ε : {r : ℝ // 0 < r},
      Real.exp (Real.log (‖w - z‖ ^ 2 + ε.val) / 2) =
        Real.sqrt (‖w - z‖ ^ 2 + ε.val) := by
    intro ε
    exact exp_half_log_eq_sqrt (by nlinarith [ε.property, sq_nonneg ‖w - z‖])
  simp_rw [h]
  exact iInf_sqrt_sq_add_pos _ (norm_nonneg _)


variable {A : Type*} [CStarAlgebra A]

theorem TracialState.map_real (τ : TracialState A) (r : ℝ) :
    τ (algebraMap ℝ A r) = (r : ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one,
    τ.toContinuousLinearMap.map_smul_of_tower, τ.map_one, Complex.real_smul, mul_one]

theorem fugledeKadisonDeterminant_zero (τ : TracialState A) :
    fugledeKadisonDeterminant τ 0 = 0 := by
  unfold fugledeKadisonDeterminant
  simp only [star_zero, zero_mul, zero_add, ← Algebra.algebraMap_eq_smul_one,
    CFC.log_algebraMap, TracialState.map_real, Complex.ofReal_re]
  have h : ∀ ε : {r : ℝ // 0 < r},
      Real.exp (Real.log ε.val / 2) = Real.sqrt ε.val :=
    fun ε => exp_half_log_eq_sqrt ε.property
  simp_rw [h]
  simpa using iInf_sqrt_sq_add_pos 0 le_rfl


end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_SpectralNaturality
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra

namespace Invariant233

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

lemma regularizedNormSquare_spectrum_pos (a : A) (ε : ℝ) (hε : 0 < ε) :
    ∀ x ∈ spectrum ℝ (star a * a + ε • (1 : A)), 0 < x := by
  intro x hx
  rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.add_singleton_eq] at hx
  obtain ⟨y, hy, t, ht, rfl⟩ := Set.mem_add.mp hx
  have ht' : t = ε := Set.mem_singleton_iff.mp ht
  subst t
  linarith [spectrum_star_mul_self_nonneg y hy]

lemma regularizedLog_map (φ : A →⋆ₐ[ℂ] B) (a : A) (ε : ℝ) (hε : 0 < ε) :
    φ (CFC.log (star a * a + ε • (1 : A))) =
      CFC.log (star (φ a) * φ a + ε • (1 : B)) := by
  have hp := regularizedNormSquare_spectrum_pos a ε hε
  have hc : ContinuousOn Real.log (spectrum ℝ (star a * a + ε • (1 : A))) := by
    apply Real.continuousOn_log.mono
    intro x hx
    exact ne_of_gt (hp x hx)
  have hs : IsSelfAdjoint (star a * a + ε • (1 : A)) := by
    simp [IsSelfAdjoint]
  have hφs : IsSelfAdjoint (φ (star a * a + ε • (1 : A))) := by
    change star (φ _) = φ _
    rw [← map_star, hs.star_eq]
  have hsmul : φ (ε • (1 : A)) = ε • (1 : B) := by
    calc
      φ (ε • (1 : A)) = ε • φ 1 := φ.toAlgHom.map_smul_of_tower ε 1
      _ = ε • (1 : B) := by rw [map_one]
  rw [CFC.log, φ.map_cfc Real.log _ hc (by fun_prop) hs hφs]
  simp only [map_add, map_mul, map_star, hsmul, CFC.log]

lemma regularizedLog_complex (z : ℂ) (ε : ℝ) :
    CFC.log (star z * z + ε • (1 : ℂ)) =
      (Real.log (‖z‖ ^ 2 + ε) : ℂ) := by
  have h : star z * z + ε • (1 : ℂ) =
      algebraMap ℝ ℂ (‖z‖ ^ 2 + ε) := by
    simp only [Complex.star_def, Complex.conj_mul', Complex.real_smul, mul_one,
      Complex.coe_algebraMap, Complex.ofReal_add, Complex.ofReal_pow]
  rw [h, CFC.log_algebraMap]
  rfl

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_DeterminantWeightBridge
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233

theorem ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    {f : X → ℝ} (hm : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hpos : ∀ᵐ x ∂μ, 0 < f x) (hinf : HasNegInfiniteLogIntegral μ f) :
    (⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
      (Real.exp ((∫ x, Real.log (f x ^ 2 + ε.val) ∂μ) / 2))) = 0 := by
  apply ScalarDeterminant.regularized_determinant_eq_zero hm hbound
  intro B
  obtain ⟨M, hM, hlt⟩ := exists_pos_truncated_log_integral_lt f hm
    (fun x => (hbound x).1) (fun x => (hbound x).2) hpos
    ((hasNegInfiniteLogIntegral_iff_of_ae_pos f hpos).mp hinf) (-B / 2)
  refine ⟨M, hM, ?_⟩
  linarith

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_RotationDeterminant
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem vectorFugledeKadisonDeterminant_unitary_mul (ξ : H)
    (u : unitary (H →L[ℂ] H)) (T : H →L[ℂ] H) :
    vectorFugledeKadisonDeterminant ξ ((u : H →L[ℂ] H) * T) =
      vectorFugledeKadisonDeterminant ξ T := by
  have h : star ((u : H →L[ℂ] H) * T) * ((u : H →L[ℂ] H) * T) = star T * T := by
    rw [star_mul, mul_assoc, ← mul_assoc (star (u : H →L[ℂ] H)),
      Unitary.star_mul_self_of_mem u.property]
    simp
  simp only [vectorFugledeKadisonDeterminant, h]

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductMultiplierFunctionalCalculus
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem vectorTrace_multiplier (θ : ℕ → ℝ) (g : Base → ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hg : Measurable g) (hb : ∀ x, ‖g x‖ ≤ C) :
    vectorTrace traceVector (multiplier θ g C hC hg hb) = ∫ x, g x ∂baseMeasure := by
  change inner ℂ traceVector (multiplier θ g C hC hg hb traceVector) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  have hv : traceVector =ᵐ[baseMeasure]
      fun _ => lp.single 2 (0 : ℤ) (1 : ℂ) := Lp.coeFn_const 2 baseMeasure _
  filter_upwards [hv, multiplier_coordinates_ae θ g C hC hg hb traceVector] with x hv hm
  rw [hv, lp.inner_single_left]
  rw [hm 0, hv]
  simp
  congr 1
  funext i
  simp [Invariant233.ProductModel.rotationIterate]

section ContinuousValues
variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
  [MeasurableSpace Y] [BorelSpace Y]

theorem vectorTrace_continuousValueRepresentation (θ : ℕ → ℝ)
    (a : Base → Y) (ha : Measurable a) (f : C(Y, ℂ)) :
    vectorTrace traceVector (continuousValueRepresentation θ a ha f) =
      ∫ x, f (a x) ∂baseMeasure :=
  vectorTrace_multiplier θ (fun x => f (a x)) ‖f‖ (norm_nonneg f)
    (f.continuous.measurable.comp ha) (fun x => f.norm_coe_le_norm (a x))

end ContinuousValues
end Invariant233.ProductModel

namespace Invariant233

theorem vectorFugledeKadisonDeterminant_composed_representation
    {H X Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [MeasurableSpace X] [TopologicalSpace Y] [CompactSpace Y]
    (μ : Measure X) (a : X → Y)
    (π : C(Y, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hξ : ∀ g : C(Y, ℂ), vectorTrace ξ (π g) = ∫ x, g (a x) ∂μ)
    (f : C(Y, ℂ)) :
    vectorFugledeKadisonDeterminant ξ (π f) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (‖f (a x)‖ ^ 2 + ε.val) ∂μ) / 2)) := by
  let : NormedAlgebra ℝ C(Y, ℂ) := NormedAlgebra.restrictScalars ℝ ℂ C(Y, ℂ)
  unfold vectorFugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  rw [← regularizedLog_map π f ε.val ε.property, hξ]
  have hpoint : ∀ y, (CFC.log (star f * f + ε.val • (1 : C(Y, ℂ)))) y =
      (Real.log (‖f y‖ ^ 2 + ε.val) : ℂ) := by
    intro y
    have h := regularizedLog_map (ContinuousMap.evalStarAlgHom ℂ ℂ y) f ε.val ε.property
    simpa only [ContinuousMap.evalStarAlgHom_apply] using
      h.trans (regularizedLog_complex (f y) ε.val)
  simp_rw [hpoint]
  rw [integral_complex_ofReal]
  rfl

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductNorm
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology ENNReal

namespace Invariant233.ProductNorm

theorem floor_lower_bound (x t : ℝ) (hx : 0 ≤ x) :
    t - 1 ≤ (⌊x + t⌋ : ℝ) := by
  have h := Int.sub_one_lt_floor (x + t)
  linarith

theorem finite_cost_lower_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hx : ∀ i ∈ I, 0 ≤ x i) :
    (n : ℝ) * (∑ i ∈ I, c i * θ i) - (∑ i ∈ I, c i) ≤
      ∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ) := by
  calc
    (n : ℝ) * (∑ i ∈ I, c i * θ i) - (∑ i ∈ I, c i) =
        ∑ i ∈ I, c i * ((n : ℝ) * θ i - 1) := by
      simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, mul_one]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (floor_lower_bound (x i) ((n : ℝ) * θ i) (hx i hi))
        (hc i hi)

theorem finite_weight_upper_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i ∈ I, 0 ≤ c i) (hx : ∀ i ∈ I, 0 ≤ x i) :
    Real.exp (-(∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  apply Real.exp_le_exp.mpr
  have h := finite_cost_lower_bound I c x θ n hc hx
  linarith

theorem infinite_weight_upper_bound {ι : Type*} (I : Finset ι)
    (c x θ : ι → ℝ) (n : ℕ)
    (hc : ∀ i, 0 ≤ c i) (hx : ∀ i, 0 ≤ x i) (hθ : ∀ i, 0 ≤ θ i)
    (hsum : Summable (fun i => c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) :
    Real.exp (-(∑' i, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  have hcost : ∀ i, 0 ≤ c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ) := by
    intro i
    apply mul_nonneg (hc i)
    exact_mod_cast Int.floor_nonneg.mpr (add_nonneg (hx i) (mul_nonneg (Nat.cast_nonneg n) (hθ i)))
  calc
    Real.exp (-(∑' i, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) ≤
        Real.exp (-(∑ i ∈ I, c i * (⌊x i + (n : ℝ) * θ i⌋ : ℝ))) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (Summable.sum_le_tsum I (fun i _hi => hcost i) hsum)
    _ ≤ _ := finite_weight_upper_bound I c x θ n (fun i _ => hc i) (fun i _ => hx i)

theorem root_upper_bound (u C S : ℝ) (n : ℕ) (hn : 0 < n)
    (hu : 0 ≤ u) (h : u ≤ Real.exp (C - (n : ℝ) * S)) :
    u ^ (1 / (n : ℝ)) ≤ Real.exp (C / (n : ℝ) - S) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    u ^ (1 / (n : ℝ)) ≤ Real.exp (C - (n : ℝ) * S) ^ (1 / (n : ℝ)) :=
      Real.rpow_le_rpow hu h (by positivity)
    _ = Real.exp ((C - (n : ℝ) * S) * (1 / (n : ℝ))) :=
      (Real.exp_mul _ _).symm
    _ = Real.exp (C / (n : ℝ) - S) := by
      congr 1
      field_simp

theorem tendsto_root_zero_of_exponential_bounds
    (u C S : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n)
    (hbound : ∀ q n, 0 < n → u n ≤ Real.exp (C q - (n : ℝ) * S q))
    (hS : ∀ b : ℝ, ∃ q, b < S q) :
    Tendsto (fun n : ℕ => (u n) ^ (1 / (n : ℝ))) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall fun n =>
      lt_of_lt_of_le ha (Real.rpow_nonneg (hu n) _)
  · intro ε hε
    obtain ⟨q, hq⟩ := hS (1 - Real.log ε)
    have hlim : Tendsto (fun n : ℕ => C q / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (C q)
    have hevent : ∀ᶠ n : ℕ in atTop, C q / (n : ℝ) < 1 :=
      hlim.eventually (eventually_lt_nhds (by norm_num))
    filter_upwards [hevent, Filter.eventually_gt_atTop (0 : ℕ)] with n hn hnpos
    calc
      (u n) ^ (1 / (n : ℝ)) ≤ Real.exp (C q / (n : ℝ) - S q) :=
        root_upper_bound (u n) (C q) (S q) n hnpos (hu n) (hbound q n hnpos)
      _ < Real.exp (Real.log ε) := Real.exp_lt_exp.mpr (by linarith)
      _ = ε := Real.exp_log hε

theorem exists_finite_sum_gt_of_tsum_eq_top {ι : Type*}
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hdiv : (∑' i, ENNReal.ofReal (a i)) = ⊤) (b : ℝ) :
    ∃ I : Finset ι, b < ∑ i ∈ I, a i := by
  classical
  by_cases hb : 0 ≤ b
  · have hlt : ENNReal.ofReal b < ∑' i, ENNReal.ofReal (a i) := by
      rw [hdiv]
      exact ENNReal.ofReal_lt_top
    rw [ENNReal.tsum_eq_iSup_sum] at hlt
    obtain ⟨I, hI⟩ := lt_iSup_iff.mp hlt
    refine ⟨I, ?_⟩
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _hi => ha i)] at hI
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hb).mp hI
  · exact ⟨∅, by simpa using lt_of_not_ge hb⟩

end Invariant233.ProductNorm

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FieldWeightedShiftPowers
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace Invariant233.WeightedShift
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (a : X → Weight) (C : ℝ) (hC : 0 ≤ C)
  (ha : ∀ x, ‖a x‖ ≤ C)
  (hm : ∀ k, AEStronglyMeasurable (fun x => a x k) μ)

theorem fieldOperator_ae (f : Lp Hilbert 2 μ) :
    fieldOperator a C hC ha hm f =ᵐ[μ] fun x => operator (a x) (f x) := by
  filter_upwards [fieldShift_ae 1 (fieldDiagonal a C hC ha hm f),
    fieldDiagonal_ae a C hC ha hm f] with x hs hd
  change ((shift 1).toLinearIsometry.toContinuousLinearMap.compLpL 2 μ
    (fieldDiagonal a C hC ha hm f)) x = operator (a x) (f x)
  rw [hs, hd]
  rfl

theorem fieldOperator_pow_ae (n : ℕ) (f : Lp Hilbert 2 μ) :
    ((fieldOperator a C hC ha hm)^n) f =ᵐ[μ]
      fun x => ((operator (a x))^n) (f x) := by
  induction n with
  | zero => exact Filter.Eventually.of_forall (fun _ => rfl)
  | succ n ih =>
    filter_upwards [fieldOperator_ae a C hC ha hm
      (((fieldOperator a C hC ha hm)^n) f), ih] with x hx hn
    simpa only [pow_succ', mul_apply_eq_comp, hn] using hx

theorem norm_fieldOperator_pow_le (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ᵐ x ∂μ, ∀ k : ℤ,
      ‖∏ j ∈ Finset.range n, a x (k + j)‖ ≤ B) :
    ‖(fieldOperator a C hC ha hm)^n‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ hB
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [fieldOperator_pow_ae a C hC ha hm n f, hprod] with x hx hb
  rw [hx]
  exact ((operator (a x))^n).le_of_opNorm_le
    (norm_operator_pow_le (a x) n hB hb) (f x)

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductQuasinilpotent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.rotationIterate_zero _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Function Filter
open scoped ENNReal BigOperators Topology

namespace Invariant233.ProductModel

theorem weight_orbit_product_eq_cocycleVersion
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (s : Set Base) (hinv : ∀ k : ℤ, ProductCocycle.rotate θ k ⁻¹' s = s)
    (hs : ∀ x ∈ s, ∀ k : ℤ, HasFiniteSupport
      (fun i ↦ ⌊ProductCocycle.representative (x i) + (k : ℝ) * θ i⌋))
    (hlaw : ∀ x ∈ s, ∀ k n : ℤ,
      ProductCocycle.cocycleVersion θ c (k + n) x =
        ProductCocycle.cocycleVersion θ c n (ProductCocycle.rotate θ k x) *
          ProductCocycle.cocycleVersion θ c k x)
    (x : Base) (hx : x ∈ s) (n : ℕ) :
    (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ j x)) =
      ProductCocycle.cocycleVersion θ c n x := by
  have hweight (k : ℤ) : weight θ c (rotationIterate θ k x) =
      ProductCocycle.cocycleVersion θ c 1 (ProductCocycle.rotate θ k x) := by
    apply weight_eq_cocycleVersion_of_finite_support θ c hθ0 hc
    have hxk : ProductCocycle.rotate θ k x ∈ s := by
      change x ∈ ProductCocycle.rotate θ k ⁻¹' s
      rw [hinv k]
      exact hx
    simpa only [ProductCocycle.representative, circleRepresentative,
      Int.cast_one, one_mul, rotationIterate, ProductCocycle.rotate] using hs _ hxk 1
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, hweight]
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using (hlaw x hx n 1).symm

theorem ae_weight_orbit_product_le
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (I : Finset ℕ) (n : ℕ) :
    ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) ≤
        Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) := by
  obtain ⟨s, _hsm, hfull, hinv, hs, hlaw⟩ :=
    ProductCocycle.exists_invariant_cocycle_core θ hθ0 hθ
  filter_upwards [hfull] with x hx k
  have hxk : ProductCocycle.rotate θ k x ∈ s := by
    change x ∈ ProductCocycle.rotate θ k ⁻¹' s
    rw [hinv k]
    exact hx
  have hprod := weight_orbit_product_eq_cocycleVersion θ c hθ0 hc s hinv hs
    (fun y hy => hlaw y hy c) (ProductCocycle.rotate θ k x) hxk n
  have hrot (j : ℕ) : rotationIterate θ (k + j) x =
      rotationIterate θ j (ProductCocycle.rotate θ k x) :=
    ProductCocycle.rotate_add θ k j x
  simp_rw [hrot]
  rw [hprod]
  apply ProductNorm.infinite_weight_upper_bound I c
    (fun i => ProductCocycle.representative (ProductCocycle.rotate θ k x i)) θ n
    hc (fun i => (ProductCocycle.representative_mem_Ico _).1) hθ0
  simpa only [Int.cast_natCast] using
    FiniteSupportCocycle.summable_weighted_int c (hs _ hxk n)

theorem norm_weightedOperator_pow_le
    (θ c : ℕ → ℝ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hprod : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      (∏ j ∈ Finset.range n, weight θ c (rotationIterate θ (k + j) x)) ≤ B) :
    ‖weightedOperator θ c ^ n‖ ≤ B := by
  unfold weightedOperator multiplier shiftOperator
  apply WeightedShift.norm_fieldOperator_pow_le
    (multiplierField θ (fun x => (weight θ c x : ℂ)) 1 _) 1 _ _ _ n hB
  filter_upwards [hprod] with x hx k
  change ‖∏ j ∈ Finset.range n,
    (weight θ c (rotationIterate θ (k + j) x) : ℂ)‖ ≤ B
  rw [← Complex.ofReal_prod, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Finset.prod_nonneg (fun j _hj => (weight_mem_Icc θ c _).1))]
  exact hx k

theorem norm_weightedOperator_pow_le_finite_cost
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ) (I : Finset ℕ) (n : ℕ) :
    ‖weightedOperator θ c ^ n‖ ≤
      Real.exp ((∑ i ∈ I, c i) - (n : ℝ) * (∑ i ∈ I, c i * θ i)) :=
  norm_weightedOperator_pow_le θ c n (Real.exp_nonneg _)
    (ae_weight_orbit_product_le θ c hθ0 hc hθ I n)

theorem weightedOperator_normQuasinilpotent
    (θ c : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hdiv : (∑' i, ENNReal.ofReal (c i * θ i)) = ∞) :
    NormQuasinilpotent (weightedOperator θ c) := by
  classical
  have hex : ∀ q : ℕ, ∃ I : Finset ℕ, (q : ℝ) < ∑ i ∈ I, c i * θ i := by
    intro q
    exact ProductNorm.exists_finite_sum_gt_of_tsum_eq_top (fun i => c i * θ i)
      (fun i => mul_nonneg (hc i) (hθ0 i)) hdiv q
  choose I hI using hex
  apply ProductNorm.tendsto_root_zero_of_exponential_bounds
    (fun n => ‖weightedOperator θ c ^ n‖)
    (fun q => ∑ i ∈ I q, c i) (fun q => ∑ i ∈ I q, c i * θ i)
    (fun n => norm_nonneg _)
  · intro q n _hn
    exact norm_weightedOperator_pow_le_finite_cost θ c hθ0 hc hθ (I q) n
  · intro b
    obtain ⟨q, hq⟩ := exists_nat_gt b
    exact ⟨q, hq.trans (hI q)⟩

theorem weightedOperator_normQuasinilpotent_of_logIntegral
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    NormQuasinilpotent (weightedOperator θ c) :=
  weightedOperator_normQuasinilpotent θ c (fun i => (hθ01 i).1) hc hθ
    ((hasNegInfiniteLogIntegral_iff_tsum θ c hθ01 hc).mp hlog)

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductDeterminant
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.ProductModel

theorem weightValue_representation_coordinate (θ c : ℕ → ℝ) :
    continuousValueRepresentation θ (weightValue θ c) (measurable_weightValue θ c)
      intervalCoordinate = weightMultiplier θ c := by
  apply multiplier_operator_ext
  intro ξ
  have hleft := continuousValueMultiplier_coordinates_ae θ (weightValue θ c)
    (measurable_weightValue θ c) intervalCoordinate ξ
  have hright : ∀ᵐ x ∂baseMeasure, ∀ k : ℤ,
      weightMultiplier θ c ξ x k =
        (weight θ c (rotationIterate θ k x) : ℂ) * ξ x k :=
    multiplier_coordinates_ae θ _ _ _ _ _ ξ
  filter_upwards [hleft, hright] with x hl hr
  intro k
  exact (hl k).trans (hr k).symm

theorem weightMultiplier_vectorDeterminant_formula (θ c : ℕ → ℝ) :
    vectorFugledeKadisonDeterminant traceVector (weightMultiplier θ c) =
      ⨅ ε : {r : ℝ // 0 < r}, ENNReal.ofReal
        (Real.exp ((∫ x, Real.log (weight θ c x ^ 2 + ε.val) ∂baseMeasure) / 2)) := by
  rw [← weightValue_representation_coordinate θ c]
  rw [vectorFugledeKadisonDeterminant_composed_representation baseMeasure
    (weightValue θ c)
    (continuousValueRepresentation θ (weightValue θ c) (measurable_weightValue θ c))
    traceVector (vectorTrace_continuousValueRepresentation θ (weightValue θ c)
      (measurable_weightValue θ c)) intervalCoordinate]
  have hn : ∀ x, ‖intervalCoordinate (weightValue θ c x)‖ = weight θ c x := by
    intro x
    simp only [intervalCoordinate, ContinuousMap.coe_mk, weightValue,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (weight_mem_Icc θ c x).1]
  simp_rw [hn]

theorem weightMultiplier_vectorDeterminant_zero (θ c : ℕ → ℝ)
    (hpos : ∀ᵐ x ∂baseMeasure, 0 < weight θ c x)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightMultiplier θ c) = 0 := by
  rw [weightMultiplier_vectorDeterminant_formula]
  exact ScalarDeterminant.regularized_determinant_eq_zero_of_log_integral
    (measurable_weight θ c) (weight_mem_Icc θ c) hpos hinf

theorem shiftOperator_mem_unitary :
    shiftOperator ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.fieldShift_mem_unitary 1

theorem weightedOperator_vectorDeterminant_zero_of_ae_pos (θ c : ℕ → ℝ)
    (hpos : ∀ᵐ x ∂baseMeasure, 0 < weight θ c x)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 := by
  let u : unitary (Hilbert →L[ℂ] Hilbert) := ⟨shiftOperator, shiftOperator_mem_unitary⟩
  change vectorFugledeKadisonDeterminant traceVector
    ((u : Hilbert →L[ℂ] Hilbert) * weightMultiplier θ c) = 0
  rw [vectorFugledeKadisonDeterminant_unitary_mul]
  exact weightMultiplier_vectorDeterminant_zero θ c hpos hinf

theorem weightedOperator_vectorDeterminant_zero (θ c : ℕ → ℝ)
    (hθ0 : ∀ i, 0 ≤ θ i) (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hinf : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) = 0 :=
  weightedOperator_vectorDeterminant_zero_of_ae_pos θ c
    (ae_weight_pos θ c hθ0 hc hθ) hinf

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_VectorSpectral
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Invariant233
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem IsFaithfulTracialVector.determinant_eq_vector
    {M : VonNeumannAlgebra H} {ξ : H} (h : IsFaithfulTracialVector M ξ) (a : M) :
    fugledeKadisonDeterminant h.toTracialState a =
      vectorFugledeKadisonDeterminant ξ (a : H →L[ℂ] H) := by
  unfold fugledeKadisonDeterminant vectorFugledeKadisonDeterminant
  apply iInf_congr
  intro ε
  have hmap : ((CFC.log (star a * a + ε.val • (1 : M)) : M) : H →L[ℂ] H) =
      CFC.log (star (a : H →L[ℂ] H) * (a : H →L[ℂ] H) + ε.val • (1 : H →L[ℂ] H)) :=
    regularizedLog_map M.toStarSubalgebra.subtype a ε.val ε.property
  change ENNReal.ofReal (Real.exp ((vectorTrace ξ
    ((CFC.log (star a * a + ε.val • (1 : M)) : M) : H →L[ℂ] H)).re / 2)) = _
  rw [hmap]

theorem IsFaithfulTracialVector.isBrownMeasure_iff_vector
    {M : VonNeumannAlgebra H} {ξ : H} (h : IsFaithfulTracialVector M ξ)
    (a : M) (μ : Measure ℂ) :
    IsBrownMeasure h.toTracialState a μ ↔
      IsVectorBrownMeasure ξ (a : H →L[ℂ] H) μ := by
  unfold IsBrownMeasure IsVectorBrownMeasure
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro z
  rw [h.determinant_eq_vector]
  rfl

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductTracialInputs
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.ProductModel

theorem weightedElement_normQuasinilpotent (θ c : ℕ → ℝ)
    (hT : NormQuasinilpotent (weightedOperator θ c)) :
    NormQuasinilpotent (weightedElement θ c) := by
  exact hT

theorem productTracialState_weightedElement_pow_eq_zero (θ c : ℕ → ℝ)
    (n : ℕ) (hn : 0 < n) :
    productTracialState θ (weightedElement θ c ^ n) = 0 := by
  exact vectorTrace_weightedOperator_pow_eq_zero θ c n hn

theorem weightedElement_determinant_eq_vector (θ c : ℕ → ℝ) :
    fugledeKadisonDeterminant (productTracialState θ) (weightedElement θ c) =
      vectorFugledeKadisonDeterminant traceVector (weightedOperator θ c) :=
  (traceVector_faithfulTracial θ).determinant_eq_vector (weightedElement θ c)

theorem weightedElement_isBrownMeasure_iff_vector (θ c : ℕ → ℝ) (μ : Measure ℂ) :
    IsBrownMeasure (productTracialState θ) (weightedElement θ c) μ ↔
      IsVectorBrownMeasure traceVector (weightedOperator θ c) μ :=
  (traceVector_faithfulTracial θ).isBrownMeasure_iff_vector (weightedElement θ c) μ

theorem weightedElement_tracialInputs_of_logIntegral (θ c : ℕ → ℝ)
    (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hθ : Summable θ)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    NormQuasinilpotent (weightedElement θ c) ∧
      (∀ n : ℕ, 0 < n → productTracialState θ (weightedElement θ c ^ n) = 0) ∧
      fugledeKadisonDeterminant (productTracialState θ) (weightedElement θ c) = 0 := by
  refine ⟨weightedElement_normQuasinilpotent θ c
    (weightedOperator_normQuasinilpotent_of_logIntegral θ c hθ01 hc hθ hlog),
    productTracialState_weightedElement_pow_eq_zero θ c, ?_⟩
  rw [weightedElement_determinant_eq_vector]
  exact weightedOperator_vectorDeterminant_zero θ c (fun i => (hθ01 i).1) hc hθ hlog

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_DeterminantHomogeneity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ENNReal CStarAlgebra
namespace Invariant233

section CStar
variable {A : Type*} [CStarAlgebra A]

theorem star_smul_mul_smul (z : ℂ) (a : A) :
    star (z • a) * (z • a) = ‖z‖ ^ 2 • (star a * a) := by
  rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [show star z * z = (‖z‖ ^ 2 : ℝ) by
    simpa only [Complex.star_def, Complex.ofReal_pow] using Complex.conj_mul' z]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ) _ _).symm

theorem regularizedLog_smul (z : ℂ) (hz : z ≠ 0) (a : A) (ε : ℝ) (hε : 0 < ε) :
    CFC.log (star (z • a) * (z • a) + (‖z‖ ^ 2 * ε) • (1 : A)) =
      algebraMap ℝ A (2 * Real.log ‖z‖) +
        CFC.log (star a * a + ε • (1 : A)) := by
  rw [star_smul_mul_smul, mul_smul, ← smul_add]
  rw [CFC.log_smul _ (fun x hx => ne_of_gt (regularizedNormSquare_spectrum_pos a ε hε x hx))
    (pow_ne_zero _ (norm_ne_zero_iff.mpr hz)) (by simp [IsSelfAdjoint])]
  rw [Real.log_pow]
  norm_num

theorem fugledeKadisonDeterminant_smul (τ : TracialState A) (z : ℂ) (a : A) :
    fugledeKadisonDeterminant τ (z • a) =
      ENNReal.ofReal ‖z‖ * fugledeKadisonDeterminant τ a := by
  by_cases hz : z = 0
  · subst z
    simp [fugledeKadisonDeterminant_zero]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  unfold fugledeKadisonDeterminant
  rw [← (positiveRegularizerScale (‖z‖ ^ 2) (sq_pos_of_pos hn)).iInf_comp]
  rw [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_ne_zero_iff.mpr hn) ENNReal.ofReal_ne_top]
  apply iInf_congr
  intro ε
  change ENNReal.ofReal (Real.exp ((τ (CFC.log
    (star (z • a) * (z • a) + (‖z‖ ^ 2 * ε.val) • (1 : A)))).re / 2)) = _
  rw [regularizedLog_smul z hz a ε.val ε.property]
  rw [map_add, TracialState.map_real]
  simp only [Complex.add_re, Complex.ofReal_re]
  rw [show (2 * Real.log ‖z‖ + (τ (CFC.log (star a * a + ε.val • (1 : A)))).re) / 2 =
      Real.log ‖z‖ + (τ (CFC.log (star a * a + ε.val • (1 : A)))).re / 2 by ring]
  rw [Real.exp_add, Real.exp_log hn, ENNReal.ofReal_mul hn.le]

end CStar

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_BrownDiracReduction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233

section Algebra
variable {A : Type*} [CStarAlgebra A]

theorem sub_scalar_eq_neg_smul_normalized (a : A) (z : ℂ) (hz : z ≠ 0) :
    a - algebraMap ℂ A z = (-z) • (1 - z⁻¹ • a) := by
  rw [smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hz]
  simp [Algebra.algebraMap_eq_smul_one, neg_smul, sub_eq_add_neg, add_comm]

theorem fugledeKadisonDeterminant_sub_scalar (τ : TracialState A)
    (a : A) (z : ℂ) (hz : z ≠ 0) :
    fugledeKadisonDeterminant τ (a - algebraMap ℂ A z) =
      ENNReal.ofReal ‖z‖ * fugledeKadisonDeterminant τ (1 - z⁻¹ • a) := by
  rw [sub_scalar_eq_neg_smul_normalized a z hz, fugledeKadisonDeterminant_smul,
    norm_neg]

theorem isBrownMeasure_dirac_zero_iff (τ : TracialState A) (a : A) :
    IsBrownMeasure τ a (Measure.dirac 0) ↔
      fugledeKadisonDeterminant τ a = 0 ∧
        ∀ z : ℂ, z ≠ 0 → fugledeKadisonDeterminant τ (1 - z⁻¹ • a) = 1 := by
  constructor
  · rintro ⟨_, _, h⟩
    constructor
    · simpa [logarithmicPotentialDeterminant_dirac] using h 0
    · intro z hz
      have hz' := h z
      rw [fugledeKadisonDeterminant_sub_scalar τ a z hz,
        logarithmicPotentialDeterminant_dirac] at hz'
      simp only [zero_sub, norm_neg] at hz'
      exact (ENNReal.mul_eq_left
        (ENNReal.ofReal_ne_zero_iff.mpr (norm_pos_iff.mpr hz))
        ENNReal.ofReal_ne_top).mp hz'
  · rintro ⟨hzero, hnormalized⟩
    refine ⟨inferInstance, ?_, ?_⟩
    · have hs : (Measure.dirac (0 : ℂ)).support ⊆ ({0} : Set ℂ) :=
        Measure.support_subset_of_isClosed isClosed_singleton (by simp)
      exact isCompact_singleton.of_isClosed_subset Measure.isClosed_support hs
    · intro z
      by_cases hz : z = 0
      · subst z
        simpa [logarithmicPotentialDeterminant_dirac] using hzero
      · rw [fugledeKadisonDeterminant_sub_scalar τ a z hz, hnormalized z hz,
          mul_one, logarithmicPotentialDeterminant_dirac]
        simp

end Algebra

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_InvertibleDeterminant
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal CStarAlgebra
namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem log_le_log_add_smul_one {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (a : A) (hA : IsStrictlyPositive a)
    (ε : ℝ) (hε : 0 ≤ ε) :
    CFC.log a ≤ CFC.log (a + ε • (1 : A)) := by
  have hsa : IsSelfAdjoint a := hA.isSelfAdjoint
  have hshift : cfc (fun x : ℝ => x + ε) a = a + ε • (1 : A) := by
    rw [cfc_add_const ε (fun x : ℝ => x) a (by fun_prop) hsa,
      cfc_id' (R := ℝ) a hsa]
    rw [Algebra.algebraMap_eq_smul_one]
  have hc : ContinuousOn Real.log ((fun x : ℝ => x + ε) '' spectrum ℝ a) := by
    apply Real.continuousOn_log.mono
    rintro x ⟨y, hy, rfl⟩
    exact ne_of_gt (lt_of_lt_of_le (hA.spectrum_pos hy) (le_add_of_nonneg_right hε))
  rw [CFC.log, CFC.log, ← hshift, ← cfc_comp Real.log (fun x : ℝ => x + ε) a hsa hc]
  apply cfc_mono
  · intro x hx
    exact Real.log_le_log (hA.spectrum_pos hx) (le_add_of_nonneg_right hε)
  · exact Real.continuousOn_log.mono (fun x hx => (hA.spectrum_pos hx).ne')
  · exact hc.comp (by fun_prop) (fun x hx => ⟨x, hx, rfl⟩)

theorem tendsto_log_add_one_div {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (a : A) (hA : IsStrictlyPositive a) :
    Tendsto (fun n : ℕ => CFC.log (a + (1 / ((n : ℝ) + 1)) • (1 : A)))
      atTop (𝓝 (CFC.log a)) := by
  have hscalar : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => a + (1 / ((n : ℝ) + 1)) • (1 : A))
      atTop (𝓝 a) := by
    simpa using (tendsto_const_nhds (x := a)).add
      (hscalar.smul (tendsto_const_nhds (x := (1 : A))))
  apply (CFC.continuousOn_log a ⟨hA.isSelfAdjoint, hA.isUnit⟩).tendsto.comp
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨hlim, Filter.Eventually.of_forall fun n => ?_⟩
  have hp : IsStrictlyPositive (a + (1 / ((n : ℝ) + 1)) • (1 : A)) :=
    hA.add_nonneg (smul_nonneg (by positivity) zero_le_one)
  exact ⟨hp.isSelfAdjoint, hp.isUnit⟩

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_TracialInvertibleDeterminant
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal CStarAlgebra
namespace Invariant233

variable {A : Type*} [CStarAlgebra A]

theorem TracialState.re_nonneg {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : TracialState A)
    {a : A} (ha : 0 ≤ a) : 0 ≤ (τ a).re := by
  have h := τ.positive (CFC.sqrt a)
  rw [(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq, CFC.sqrt_mul_sqrt_self a ha] at h
  exact h

theorem TracialState.re_mono {A : Type*} [CStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] (τ : TracialState A)
    {a b : A} (hab : a ≤ b) : (τ a).re ≤ (τ b).re := by
  have h := τ.re_nonneg (sub_nonneg.mpr hab)
  change 0 ≤ (τ.toContinuousLinearMap (b - a)).re at h
  simpa only [map_sub, Complex.sub_re, sub_nonneg] using h

theorem fugledeKadisonDeterminant_of_isUnit (τ : TracialState A) (a : A)
    (ha : IsUnit a) :
    fugledeKadisonDeterminant τ a =
      ENNReal.ofReal (Real.exp ((τ (CFC.log (star a * a))).re / 2)) := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hp : IsStrictlyPositive (star a * a) :=
    ⟨star_mul_self_nonneg a, ha.star.mul ha⟩
  have hcont : Continuous (fun b : A =>
      ENNReal.ofReal (Real.exp ((τ b).re / 2))) := by
    apply ENNReal.continuous_ofReal.comp
    fun_prop
  have hlim := hcont.continuousAt.tendsto.comp (tendsto_log_add_one_div (star a * a) hp)
  unfold fugledeKadisonDeterminant
  apply le_antisymm
  · apply ge_of_tendsto' hlim
    intro n
    exact iInf_le _ (⟨1 / ((n : ℝ) + 1), by positivity⟩ : {r : ℝ // 0 < r})
  · apply le_iInf
    intro ε
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply div_le_div_of_nonneg_right _ (by norm_num)
    exact τ.re_mono (log_le_log_add_smul_one (star a * a) hp ε.val ε.property.le)

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_QuasinilpotentDeterminantReduction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233
open scoped ENNReal

theorem NormQuasinilpotent.isUnit_one_sub_smul
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    {T : A} (hT : NormQuasinilpotent T) (z : ℂ) : IsUnit (1 - z • T) := by
  have hi := hT.geometric_inverse_identities z
  exact ⟨⟨1 - z • T, (∑' n : ℕ, z ^ n • T ^ n), hi.2, hi.1⟩, rfl⟩

theorem fugledeKadisonDeterminant_one_sub_smul_of_normQuasinilpotent
    {A : Type*} [CStarAlgebra A] (τ : TracialState A) {T : A}
    (hT : NormQuasinilpotent T) (z : ℂ) :
    fugledeKadisonDeterminant τ (1 - z • T) =
      ENNReal.ofReal (Real.exp ((τ (CFC.log
        (star (1 - z • T) * (1 - z • T)))).re / 2)) :=
  fugledeKadisonDeterminant_of_isUnit τ _ (hT.isUnit_one_sub_smul z)

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_QuasinilpotentTraceDerivative
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233

section BanachAlgebra
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

theorem inverse_one_sub_smul_mul_moment_zero (φ : A →L[ℂ] ℂ) {T : A}
    (hT : NormQuasinilpotent T) (hmom : ∀ n : ℕ, 0 < n → φ (T ^ n) = 0)
    (z : ℂ) : φ (Ring.inverse (1 - z • T) * T) = 0 := by
  rw [hT.inverse_one_sub_smul z, ← (hT.summable_smul_pow z).tsum_mul_right T,
    φ.map_tsum ((hT.summable_smul_pow z).mul_right T)]
  have hz (n : ℕ) : φ ((z ^ n • T ^ n) * T) = 0 := by
    rw [smul_mul_assoc, ← pow_succ, map_smul, hmom (n + 1) (Nat.succ_pos n), smul_zero]
  simp only [hz, tsum_zero]

end BanachAlgebra

namespace TracialState
variable {A : Type*} [CStarAlgebra A]

theorem inverse_one_sub_smul_mul_eq_zero (τ : TracialState A) {T : A}
    (hT : NormQuasinilpotent T) (hmom : ∀ n : ℕ, 0 < n → τ (T ^ n) = 0)
    (z : ℂ) : τ (Ring.inverse (1 - z • T) * T) = 0 :=
  inverse_one_sub_smul_mul_moment_zero τ.toContinuousLinearMap hT hmom z

theorem inverse_one_sub_smul_mul_smul_eq_zero (τ : TracialState A) {T : A}
    (hT : NormQuasinilpotent T) (hmom : ∀ n : ℕ, 0 < n → τ (T ^ n) = 0)
    (z w : ℂ) : τ (Ring.inverse (1 - z • T) * (w • T)) = 0 := by
  rw [mul_smul_comm, map_smul, τ.inverse_one_sub_smul_mul_eq_zero hT hmom z,
    smul_zero]

end TracialState
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_QuasinilpotentBrown
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal CStarAlgebra
namespace Invariant233
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

theorem re_trace_log_normalized_resolvent_eq_zero (τ : TracialState A) {a : A}
    (hQN : NormQuasinilpotent a) (hmom : ∀ n : ℕ, 0 < n → τ (a^n) = 0) (z : ℂ) :
    (τ (CFC.log (star (1-z • a) * (1-z • a)))).re = 0 := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let b : ℝ → A := fun t => 1-t • (z • a)
  let F : ℝ → ℝ := fun t => (τ (CFC.log (star (b t) * b t))).re
  have hunit : ∀ t, IsUnit (b t) := by
    intro t
    simpa only [b, mul_smul, Complex.coe_smul] using
      hQN.isUnit_one_sub_smul ((t : ℂ)*z)
  have hb : ∀ t, HasDerivAt b (-(z • a)) t := by
    intro t
    simpa only [b, one_smul, id_eq] using
      ((hasDerivAt_id t).smul_const (z • a)).const_sub (1 : A)
  have hF : ∀ t, HasDerivAt F 0 t := by
    intro t
    have h := CFCLogSeries.hasDerivAt_re_trace_log_normSquare τ hunit hb
      (continuousAt_const : ContinuousAt (fun _ : ℝ => -(z • a)) t)
    have hz : τ (Ring.inverse (b t) * (-(z • a))) = 0 := by
      simpa only [b, mul_smul, Complex.coe_smul, neg_smul] using
        τ.inverse_one_sub_smul_mul_smul_eq_zero hQN hmom ((t : ℂ)*z) (-z)
    simpa only [F, hz, Complex.zero_re, mul_zero] using h
  have hconst := is_const_of_deriv_eq_zero
    (fun t => (hF t).differentiableAt) (fun t => (hF t).deriv) (1 : ℝ) 0
  simpa [F, b, CFC.log_one] using hconst

theorem fugledeKadisonDeterminant_normalized_resolvent_eq_one
    (τ : TracialState A) {a : A} (hQN : NormQuasinilpotent a)
    (hmom : ∀ n : ℕ, 0 < n → τ (a^n) = 0) (z : ℂ) :
    fugledeKadisonDeterminant τ (1-z • a) = 1 := by
  rw [fugledeKadisonDeterminant_one_sub_smul_of_normQuasinilpotent τ hQN,
    re_trace_log_normalized_resolvent_eq_zero τ hQN hmom]
  simp

theorem isBrownMeasure_dirac_zero_of_normQuasinilpotent_of_moments_zero
    (τ : TracialState A) {a : A} (hQN : NormQuasinilpotent a)
    (hmom : ∀ n : ℕ, 0 < n → τ (a^n) = 0)
    (hdet : fugledeKadisonDeterminant τ a = 0) :
    IsBrownMeasure τ a (Measure.dirac 0) := by
  apply (isBrownMeasure_dirac_zero_iff τ a).mpr
  exact ⟨hdet, fun z _ => fugledeKadisonDeterminant_normalized_resolvent_eq_one τ hQN hmom z⁻¹⟩

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Spectral_ProductBrownMeasure
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set

namespace Invariant233.ProductModel

private theorem factor_nontrivial_of_trace (θ : ℕ → ℝ) : Nontrivial (factor θ) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have ht := congrArg (productTracialState θ).toContinuousLinearMap h
  rw [map_zero, (productTracialState θ).map_one] at ht
  exact zero_ne_one ht

theorem weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral_oai
    (θ c : ℕ → ℝ) (hθ01 : ∀ i, θ i ∈ Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hθ : Summable θ)
    (hlog : HasNegInfiniteLogIntegral baseMeasure (weight θ c)) :
    IsVectorBrownMeasure traceVector (weightedOperator θ c) (Measure.dirac 0) := by
  let := factor_nontrivial_of_trace θ
  obtain ⟨hqn, hmom, hdet⟩ :=
    weightedElement_tracialInputs_of_logIntegral θ c hθ01 hc hθ hlog
  exact (weightedElement_isBrownMeasure_iff_vector θ c _).mp
    (isBrownMeasure_dirac_zero_of_normQuasinilpotent_of_moments_zero
      (productTracialState θ) hqn hmom hdet)

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral_oai := @OAI.Invariant233.ProductModel.weightedOperator_isVectorBrownMeasure_dirac_zero_of_logIntegral_oai
