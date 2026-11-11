-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.factor_complete
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:27:00.534149+00:00
-- url     : https://prove2.me/submissions/c959adb7-1797-4d04-9c76-35057c922c2e

import Mathlib
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.NormedSpace
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Sequences
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_ProductModel_factor_isTypeII1FactorWithVector

section
-- module Solutions.Q234_IR.Compat
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {c : Prop} {_ : Decidable c} {a b : α} (h : c) :
    (if c then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualSeparable
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual
universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem continuous_vectorFunctional (M : VonNeumannAlgebra H) :
    Continuous (fun xy : H × H => vectorFunctional M xy.1 xy.2) := by
  exact (((innerSL ℂ).continuous.comp continuous_fst).clm_comp
    ((ContinuousLinearMap.apply ℂ H).continuous.comp continuous_snd)).clm_comp_const
      M.toSubalgebra.toSubmodule.subtypeL

theorem isSeparable_predual (M : VonNeumannAlgebra H)
    [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.IsSeparable (predual M : Set (StrongDual ℂ M)) := by
  exact ((TopologicalSpace.isSeparable_range (continuous_vectorFunctional M)).span).closure

instance separableSpace_predual (M : VonNeumannAlgebra H)
    [TopologicalSpace.SeparableSpace H] :
    TopologicalSpace.SeparableSpace (predual M) :=
  (isSeparable_predual M).separableSpace

end Invariant233.ConcretePredual

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualComplete
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ConcretePredual

universe u
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

attribute [local instance] OAI.Invariant233.ConcretePredual.completedPredualNormedAddCommGroup
attribute [local instance] OAI.Invariant233.ConcretePredual.completedPredualNormedSpace
theorem hasSeparablePredual (M : VonNeumannAlgebra H)
    [TopologicalSpace.SeparableSpace H] : HasSeparablePredual M := by
  let : CompleteSpace (predual M) := by
    unfold predual
    infer_instance
  exact ⟨predual M, inferInstance, inferInstance, inferInstance, inferInstance,
    ⟨(evaluationLinearIsometryEquiv M).symm⟩⟩

end Invariant233.ConcretePredual

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_HilbertModelSize
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.HilbertModelSize

open TopologicalSpace MeasureTheory
open scoped lp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem separable_l2 (ι : Type*) [Countable ι] : SeparableSpace (ℓ²(ι, ℂ)) :=
  separable_of_countable_hilbertBasis (default : HilbertBasis ι ℂ (ℓ²(ι, ℂ)))

section BochnerLp

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]

theorem separable_L2_l2 [MeasurableSpace.CountablyGenerated X]
    (ι : Type*) [Countable ι] : SeparableSpace (Lp (ℓ²(ι, ℂ)) 2 μ) := by
  let := separable_l2 ι
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end BochnerLp

end Invariant233.HilbertModelSize

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductHilbert
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ProductModel

instance hilbert_separable : TopologicalSpace.SeparableSpace Hilbert :=
  HilbertModelSize.separable_L2_l2 baseMeasure ℤ

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConcretePredualModels
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233

theorem ProductModel.factor_hasSeparablePredual (θ : ℕ → ℝ) :
    HasSeparablePredual (ProductModel.factor θ) :=
  ConcretePredual.hasSeparablePredual _

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_GeometricAverage
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Topology
open scoped BigOperators

namespace Invariant233

theorem norm_geometric_sum_le (r : ℂ) (hr : r ≠ 1) (hrnorm : ‖r‖ = 1)
    (n : ℕ) :
    ‖∑ k ∈ Finset.range n, r ^ k‖ ≤ 2 / ‖r - 1‖ := by
  rw [geom_sum_eq hr, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖r ^ n - 1‖ ≤ ‖r ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, hrnorm]

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FejerKernel
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Invariant233.Fejer

 theorem kernel_nonneg (H : ℕ) (x : Circle) : 0 ≤ kernel H x :=
  div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

 theorem geometricPolynomial_eq_sum_pow (H : ℕ) (x : Circle) :
    geometricPolynomial H x = ∑ k ∈ Finset.range H, (fourier 1 x) ^ k := by
  apply Finset.sum_congr rfl
  intro k hk
  simp only [fourier_apply, one_zsmul]
  rw [natCast_zsmul, AddCircle.toCircle_nsmul, Circle.coe_pow]

 theorem kernel_complex_expansion (H : ℕ) (x : Circle) :
    (kernel H x : ℂ) = (H : ℂ)⁻¹ *
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x := by
  rw [kernel, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.normSq_eq_conj_mul_self]
  unfold geometricPolynomial
  rw [map_sum, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm, div_eq_inv_mul]
  simp_rw [sub_eq_add_neg, fourier_add, fourier_neg]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

 theorem integral_fourier (n : ℤ) :
    (∫ x : Circle, fourier n x ∂AddCircle.haarAddCircle) = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

 theorem integral_kernel_complex (H : ℕ) (hH : H ≠ 0) :
    (∫ x : Circle, (kernel H x : ℂ) ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [kernel_complex_expansion]
  rw [integral_const_mul]
  rw [integral_finsetSum]
  · simp_rw [integral_finsetSum _ (fun l hl => (fourier _).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_fourier]
    have hsum : (∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        (if (k : ℤ) - (l : ℤ) = 0 then (1 : ℂ) else 0)) = H := by
      simp only [sub_eq_zero, Nat.cast_inj]
      calc
        _ = ∑ k ∈ Finset.range H, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro k hk
          simp only [Finset.sum_ite_eq, hk, ite_true, if_true]
        _ = H := by simp
    rw [hsum, inv_mul_cancel₀ (by exact_mod_cast hH)]
  · intro k hk
    exact integrable_finsetSum _ (fun l hl => (fourier _).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

 theorem integral_kernel (H : ℕ) (hH : H ≠ 0) :
    (∫ x : Circle, kernel H x ∂AddCircle.haarAddCircle) = 1 := by
  have h := integral_kernel_complex H hH
  have hcast := integral_ofReal (f := kernel H) (𝕜 := ℂ)
    (μ := (AddCircle.haarAddCircle : Measure Circle))
  have hcast2 : (∫ x : Circle, (kernel H x : ℂ) ∂AddCircle.haarAddCircle) =
      Complex.ofReal (∫ x : Circle, kernel H x ∂AddCircle.haarAddCircle) := hcast
  rw [hcast2] at h
  exact_mod_cast h

 theorem integrable_fourier (n : ℤ) :
    Integrable (fun x : Circle => fourier n x) AddCircle.haarAddCircle :=
  (fourier n).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

 theorem difference_mem_frequencies {H k l : ℕ}
    (hk : k ∈ Finset.range H) (hl : l ∈ Finset.range H) :
    (k : ℤ) - (l : ℤ) ∈ frequencies H := by
  simp only [frequencies, Finset.mem_Ioo]
  simp only [Finset.mem_range] at hk hl
  omega

 theorem coefficient_expansion (H : ℕ) (n : ℤ) :
    coefficient H n = (H : ℂ)⁻¹ *
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        if (k : ℤ) - (l : ℤ) = n then (1 : ℂ) else 0 := by
  unfold coefficient
  have heq : (fun x : Circle => (kernel H x : ℂ)) = fun x =>
      (H : ℂ)⁻¹ * ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x := funext (kernel_complex_expansion H)
  rw [heq, fourierCoeff.const_mul]
  congr 1
  have houter : (fun x : Circle => ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        fourier ((k : ℤ) - (l : ℤ)) x) =
      ∑ k ∈ Finset.range H, ∑ l ∈ Finset.range H,
        (fun x : Circle => fourier ((k : ℤ) - (l : ℤ)) x) := by
    ext x
    simp
  rw [houter, fourierCoeff.sum]
  · simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [fourierCoeff.sum]
    · simp only [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro l hl
      simp only [fourierCoeff_fourier, Pi.single_apply, eq_comm]
    · intro l hl
      exact integrable_fourier _
  · intro k hk
    exact integrable_finsetSum' _ (fun l hl => integrable_fourier _)

 theorem kernel_eq_finite_fourier_sum (H : ℕ) (x : Circle) :
    (kernel H x : ℂ) = ∑ n ∈ frequencies H, coefficient H n * fourier n x := by
  rw [kernel_complex_expansion]
  symm
  simp_rw [coefficient_expansion, mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
    difference_mem_frequencies hk hl, ite_true, if_true]

 theorem kernel_le_chord_bound (H : ℕ) (x : Circle) (hx : fourier 1 x ≠ 1) :
    kernel H x ≤ 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) := by
  have hb := Invariant233.norm_geometric_sum_le (fourier 1 x) hx
    (Circle.norm_coe _) H
  rw [← geometricPolynomial_eq_sum_pow] at hb
  rw [kernel, Complex.normSq_eq_norm_sq]
  have hs : ‖geometricPolynomial H x‖ ^ 2 ≤ (2 / ‖fourier 1 x - 1‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  calc
    _ ≤ (2 / ‖fourier 1 x - 1‖) ^ 2 / H :=
      div_le_div_of_nonneg_right hs (Nat.cast_nonneg H)
    _ = 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) := by
      rw [div_pow, div_div]
      congr 1 <;> ring

 theorem chord_lower_bound_coe {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖fourier 1 (t : Circle) - 1‖ := by
  have hangle : |Real.pi * t| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hangle
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hc : 2 * (Real.pi : ℂ) * Complex.I * (1 : ℂ) * (t : ℂ) / (1 : ℂ) =
      Complex.I * ((2 * Real.pi * t : ℝ) : ℂ) := by
    push_cast
    ring
  rw [fourier_coe_apply]
  norm_num only [Complex.ofReal_one, Int.cast_one] at *
  rw [hc, Complex.norm_exp_I_mul_ofReal_sub_one]
  have hhalf : 2 * Real.pi * t / 2 = Real.pi * t := by ring
  rw [hhalf, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcanc : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [hcanc] at hsin
  linarith

 theorem chord_lower_bound (x : Circle) :
    4 * dist x 0 ≤ ‖fourier 1 x - 1‖ := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    have hround : (((round t : ℤ) : ℝ) : Circle) = 0 := by
      have hc := AddCircle.coe_zsmul (p := (1 : ℝ)) (n := round t) (x := (1 : ℝ))
      simpa only [zsmul_eq_mul, mul_one, AddCircle.coe_period, smul_zero] using hc
    have hcoe : ((t - round t : ℝ) : Circle) = (t : Circle) := by
      rw [QuotientAddGroup.mk_sub, hround, sub_zero]
    have h := chord_lower_bound_coe (abs_sub_round t)
    rw [hcoe] at h
    simpa only [dist_zero_right, UnitAddCircle.norm_eq] using h

 theorem kernel_le_distance_bound (H : ℕ) (hH : H ≠ 0)
    (x : Circle) (hx : x ≠ 0) :
    kernel H x ≤ 1 / (4 * (H : ℝ) * (dist x 0) ^ 2) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hd : 0 < dist x 0 := dist_pos.mpr hx
  have hc := chord_lower_bound x
  have hcpos : 0 < ‖fourier 1 x - 1‖ := lt_of_lt_of_le (by positivity) hc
  have hxchar : fourier 1 x ≠ 1 := by
    intro heq
    simp only [heq, sub_self, norm_zero, lt_self_iff_false] at hcpos
  calc
    kernel H x ≤ 4 / ((H : ℝ) * ‖fourier 1 x - 1‖ ^ 2) :=
      kernel_le_chord_bound H x hxchar
    _ ≤ 4 / ((H : ℝ) * (4 * dist x 0) ^ 2) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 2) hHpos.le
    _ = 1 / (4 * (H : ℝ) * (dist x 0) ^ 2) := by
      field_simp

 theorem kernel_le_of_distance_ge (H : ℕ) (hH : H ≠ 0)
    {η : ℝ} (hη : 0 < η) (x : Circle) (hx : η ≤ dist x 0) :
    kernel H x ≤ 1 / (4 * (H : ℝ) * η ^ 2) := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast Nat.pos_of_ne_zero hH
  have hx0 : x ≠ 0 := by
    intro heq
    subst x
    simp only [dist_self] at hx
    linarith
  apply (kernel_le_distance_bound H hH x hx0).trans
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hη.le hx 2) (by positivity)

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FejerBanachApproximation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Invariant233.Fejer

theorem kernel_tendstoUniformlyOn_compl
    (u : Set Circle) (hu : IsOpen u) (h0 : (0 : Circle) ∈ u) :
    TendstoUniformlyOn (fun n : ℕ => kernel (n + 1)) 0 atTop uᶜ := by
  obtain ⟨η, hη, hball⟩ := Metric.isOpen_iff.mp hu 0 h0
  have hn : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hb : Tendsto (fun n : ℕ => (1 / (4 * η ^ 2)) / (n + 1 : ℕ))
      atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds.div_atTop hn
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hb.eventually (gt_mem_nhds hε)] with n hnε
  intro x hx
  have hdist : η ≤ dist x 0 := by
    by_contra h
    exact hx (hball (show x ∈ Metric.ball 0 η from lt_of_not_ge h))
  have hk := kernel_le_of_distance_ge (n + 1) (Nat.succ_ne_zero n) hη x hdist
  have heq : 1 / (4 * (n + 1 : ℕ) * η ^ 2) =
      (1 / (4 * η ^ 2)) / (n + 1 : ℕ) := by ring
  rw [heq] at hk
  simpa only [Pi.zero_apply, dist_zero_left, Real.norm_eq_abs,
    abs_of_nonneg (kernel_nonneg (n + 1) x)] using hk.trans_lt hnε

theorem tendsto_integral_kernel_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Circle → E} (hg : Integrable g AddCircle.haarAddCircle)
    (h0 : ContinuousAt g 0) :
    Tendsto (fun n : ℕ => ∫ t, kernel (n + 1) t • g t ∂AddCircle.haarAddCircle)
      atTop (𝓝 (g 0)) := by
  apply tendsto_integral_peak_smul_of_integrable_of_tendsto
    (t := Set.univ) MeasurableSet.univ (by simp) (measure_ne_top _ _)
  · exact Eventually.of_forall fun n t => kernel_nonneg (n + 1) t
  · exact kernel_tendstoUniformlyOn_compl
  · have heq : (fun n : ℕ => ∫ t in Set.univ, kernel (n + 1) t
        ∂AddCircle.haarAddCircle) = fun _ => (1 : ℝ) := by
      funext n
      rw [MeasureTheory.setIntegral_univ, integral_kernel (n + 1) (Nat.succ_ne_zero n)]
    rw [heq]
    exact tendsto_const_nhds
  · exact Eventually.of_forall fun n => (continuous_kernel (n + 1)).aestronglyMeasurable
  · exact hg
  · exact h0

theorem tendsto_integral_kernel_smul_of_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : Circle → E} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ t, kernel (n + 1) t • g t ∂AddCircle.haarAddCircle)
      atTop (𝓝 (g 0)) :=
  tendsto_integral_kernel_smul
    (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)) hg.continuousAt

end Invariant233.Fejer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FieldCovariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace Topology

namespace Invariant233.FieldTraceCyclic

variable {Ω E : Type*} [MeasurableSpace Ω]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {μ : Measure Ω} [IsFiniteMeasure μ]

theorem ae_covariance_of_commute [TopologicalSpace.SeparableSpace E]
    (T J : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hJ : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (J ξ) x = S (ξ (σ x)))
    (hcomm : Commute T J) :
    ∀ᵐ x ∂μ, A x * S = S * A (σ x) := by
  let v := TopologicalSpace.denseSeq E
  have hv : DenseRange v := TopologicalSpace.denseRange_denseSeq E
  have hall : ∀ᵐ x ∂μ, ∀ n : ℕ, A x (S (v n)) = S (A (σ x) (v n)) :=
    ae_all_iff.mpr (fun n => ae_covariance_apply_of_commute T J A S σ hσ hT hJ hcomm (v n))
  filter_upwards [hall] with x hx
  apply ContinuousLinearMap.ext
  intro w
  exact hv.induction_on w
    (isClosed_eq ((A x).continuous.comp S.continuous)
      (S.continuous.comp (A (σ x)).continuous)) hx

omit [IsFiniteMeasure μ] in

theorem commute_shiftedPullback_of_covariance
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (A : Ω → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : Ω → Ω) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, ∀ᵐ x ∂μ, (T ξ) x = A x (ξ x))
    (hcov : ∀ᵐ x ∂μ, A x * S = S * A (σ x)) :
    Commute T (DirectIntegral.shiftedPullback S σ hσ) := by
  change T * DirectIntegral.shiftedPullback S σ hσ =
    DirectIntegral.shiftedPullback S σ hσ * T
  apply ContinuousLinearMap.ext
  intro ξ
  apply Lp.ext
  filter_upwards [hT (DirectIntegral.shiftedPullback S σ hσ ξ),
    shiftedPullback_ae S σ hσ ξ, shiftedPullback_ae S σ hσ (T ξ),
    hσ.quasiMeasurePreserving.ae (hT ξ), hcov] with x hTx hJx hJTx hTσx hcovx
  change (T (DirectIntegral.shiftedPullback S σ hσ ξ)) x =
    (DirectIntegral.shiftedPullback S σ hσ (T ξ)) x
  rw [hTx, hJx, hJTx, hTσx]
  exact congrArg (fun R : E →L[ℂ] E => R (ξ (σ x))) hcovx

end Invariant233.FieldTraceCyclic

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
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationMeasurable
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233

theorem vonNeumannAlgebra_mem_of_strong_tendsto
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) {l : Filter ι} [l.NeBot]
    {A : ι → H →L[ℂ] H} {B : H →L[ℂ] H}
    (hA : ∀ i, A i ∈ M) (hAB : ∀ v, Tendsto (fun i => A i v) l (𝓝 (B v))) :
    B ∈ M := by
  rw [← M.commutant_commutant, VonNeumannAlgebra.mem_commutant_iff]
  intro T hT
  apply ContinuousLinearMap.ext
  intro v
  have ht := T.continuous.continuousAt.tendsto.comp (hAB v)
  have ha := hAB (T v)
  have heq : (fun i => T (A i v)) = (fun i => A i (T v)) := by
    funext i
    exact (DFunLike.congr_fun ((VonNeumannAlgebra.mem_commutant_iff.mp hT) (A i) (hA i)) v).symm
  change T (B v) = B (T v)
  change Tendsto (fun i => T (A i v)) l (𝓝 (T (B v))) at ht
  rw [heq] at ht
  exact tendsto_nhds_unique ht ha

end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFourierRecovery
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace Invariant233
namespace StrongFourierRecovery

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in

theorem average_apply
    (T : Fejer.Circle → H →L[ℂ] H)
    (hT : ∀ v : H, Continuous (fun t => T t v))
    (C : ℤ → H →L[ℂ] H)
    (hC : ∀ r v, C r v = ∫ t, fourier r t • T t v ∂AddCircle.haarAddCircle)
    (N : ℕ) (v : H) :
    average C N v = ∫ t, Fejer.kernel N t • T t v ∂AddCircle.haarAddCircle := by
  have hint (r : ℤ) : Integrable (fun t : Fejer.Circle => fourier r t • T t v)
      AddCircle.haarAddCircle :=
    ((fourier r).continuous.smul (hT v)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    average C N v = ∑ r ∈ Fejer.frequencies N,
        Fejer.coefficient N r • ∫ t, fourier r t • T t v ∂AddCircle.haarAddCircle := by
      simp only [average, sum_apply, smul_apply, hC]
    _ = ∫ t, ∑ r ∈ Fejer.frequencies N,
        Fejer.coefficient N r • (fourier r t • T t v) ∂AddCircle.haarAddCircle := by
      rw [integral_finsetSum]
      · simp only [integral_smul]
      · intro r hr
        exact (hint r).smul _
    _ = ∫ t, Fejer.kernel N t • T t v ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Eventually.of_forall fun t => by
        change (∑ r ∈ Fejer.frequencies N, Fejer.coefficient N r • (fourier r t • T t v)) =
          Fejer.kernel N t • T t v
        rw [← Complex.coe_smul, Fejer.kernel_eq_finite_fourier_sum, Finset.sum_smul]
        simp only [mul_smul]

theorem average_tendsto
    (T : Fejer.Circle → H →L[ℂ] H)
    (hT : ∀ v : H, Continuous (fun t => T t v))
    (C : ℤ → H →L[ℂ] H)
    (hC : ∀ r v, C r v = ∫ t, fourier r t • T t v ∂AddCircle.haarAddCircle)
    (v : H) :
    Tendsto (fun n : ℕ => average C (n + 1) v) atTop (𝓝 (T 0 v)) := by
  simpa only [average_apply T hT C hC] using
    Fejer.tendsto_integral_kernel_smul_of_continuous (hT v)

theorem mem_of_fourier_modes
    (M : VonNeumannAlgebra H) (T : Fejer.Circle → H →L[ℂ] H)
    (hT : ∀ v : H, Continuous (fun t => T t v))
    (C : ℤ → H →L[ℂ] H)
    (hC : ∀ r v, C r v = ∫ t, fourier r t • T t v ∂AddCircle.haarAddCircle)
    (hCm : ∀ r, C r ∈ M) : T 0 ∈ M := by
  apply vonNeumannAlgebra_mem_of_strong_tendsto M
    (l := atTop) (A := fun n : ℕ => average C (n + 1))
  · intro n
    apply M.toStarSubalgebra.sum_mem
    intro r hr
    exact M.toStarSubalgebra.smul_mem (hCm r) _
  · exact average_tendsto T hT C hC

end StrongFourierRecovery
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCovariance
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.hilbert_separable _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem field_covariance {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂baseMeasure, ∀ m : ℤ,
      F x * (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap =
        (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap *
          F (rotationIterate θ m x) := by
  let := HilbertModelSize.separable_of_countable_hilbertBasis
    (default : HilbertBasis ℤ ℂ Fiber)
  apply ae_all_iff.mpr
  intro m
  exact FieldTraceCyclic.ae_covariance_of_commute T _ F _ _
    (rotationIterate_measurePreserving θ m) hF
    (FieldTraceCyclic.shiftedPullback_ae _ _ _)
    (commute_shiftedPullback_of_mem_factor θ hT m)

theorem field_conjugacy {θ : ℕ → ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ factor θ) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : ∀ ξ : Hilbert, T ξ =ᵐ[baseMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂baseMeasure, ∀ m : ℤ,
      F (rotationIterate θ m x) =
        (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap := by
  filter_upwards [field_covariance hT F hF] with x hx m
  have hinv : (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap *
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap = 1 := by
    rw [← WeightedShift.shift_add]
    simp [WeightedShift.shift_zero]
  have heq := congrArg
    (fun A : Fiber →L[ℂ] Fiber =>
      (WeightedShift.shift (-m)).toLinearIsometry.toContinuousLinearMap * A) (hx m)
  simpa only [← mul_assoc, hinv, one_mul] using heq.symm

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductFactorSource
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.hilbert_separable _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
namespace Invariant233.ProductModel

theorem vectorTrace_eq_centralDiagonalIntegral
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hA : ∀ f : Hilbert, A f =ᵐ[baseMeasure] fun x => F x (f x)) :
    vectorTrace traceVector A = centralDiagonalIntegral F := by
  unfold vectorTrace traceVector centralDiagonalIntegral
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 baseMeasure (lp.single 2 0 (1 : ℂ) : Fiber),
    hA (Lp.const 2 baseMeasure (lp.single 2 0 (1 : ℂ) : Fiber))] with x hx hAx
  rw [hAx, hx]
  rfl

theorem IsCovariantFieldRepresentation.vectorTrace_eq
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) :
    vectorTrace traceVector A = centralDiagonalIntegral F :=
  vectorTrace_eq_centralDiagonalIntegral A F h.2.2.2.1

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductFieldRepresentation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.hilbert_separable _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.ProductModel

theorem exists_covariantFieldRepresentation {θ : ℕ → ℝ}
    {A : Hilbert →L[ℂ] Hilbert} (hA : A ∈ factor θ) :
    ∃ F : Base → Fiber →L[ℂ] Fiber,
      IsCovariantFieldRepresentation θ A F ‖A‖ := by
  obtain ⟨F, hbound, hm, hrep, _⟩ := exists_unique_field hA
  refine ⟨F, norm_nonneg A, hbound, hm, hrep, ?_⟩
  filter_upwards [field_conjugacy hA F hrep] with x hx
  have hrot : rotationIterate θ 1 x = rotation θ x := by
    funext i
    change x i + (((1 : ℤ) : ℝ) * θ i : ℝ) = x i + (θ i : Circle)
    simp only [Int.cast_one, one_mul]
  rw [← hrot]
  exact hx 1

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductFieldDiagonals
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.hilbert_separable _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.ProductModel

private theorem rotationIterate_one_eq (θ : ℕ → ℝ) (x : Base) :
    rotationIterate θ 1 x = rotation θ x := by
  funext i
  change x i + (((1 : ℤ) : ℝ) * θ i : ℝ) = x i + (θ i : Circle)
  simp only [Int.cast_one, one_mul]

theorem IsCovariantFieldRepresentation.covariance_all
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) :
    ∀ᵐ x ∂baseMeasure, ∀ m : ℤ,
      F x * S m = S m * F (rotationIterate θ m x) := by
  have hpm : S 1 * S (-1) = 1 := by
    rw [← WeightedShift.shift_add]
    norm_num [WeightedShift.shift_zero]
  have hmp : S (-1) * S 1 = 1 := by
    rw [← WeightedShift.shift_add]
    norm_num [WeightedShift.shift_zero]
  have h1 : ∀ᵐ x ∂baseMeasure, F x * S 1 = S 1 * F (rotationIterate θ 1 x) := by
    filter_upwards [h.2.2.2.2] with x hx
    rw [rotationIterate_one_eq, hx]
    simp only [← mul_assoc, hpm, one_mul]
  have hn1 : ∀ᵐ x ∂baseMeasure, F x * S (-1) = S (-1) * F (rotationIterate θ (-1) x) := by
    filter_upwards [(rotationIterate_measurePreserving θ (-1)).quasiMeasurePreserving.ae h1]
      with x hx
    have hrot : rotationIterate θ 1 (rotationIterate θ (-1) x) = x := by
      rw [← rotationIterate_add]
      norm_num
    rw [hrot] at hx
    calc
      F x * S (-1) = (S (-1) * S 1) * F x * S (-1) := by rw [hmp, one_mul]
      _ = S (-1) * (S 1 * F x) * S (-1) := by simp only [mul_assoc]
      _ = S (-1) * (F (rotationIterate θ (-1) x) * S 1) * S (-1) := by rw [← hx]
      _ = S (-1) * F (rotationIterate θ (-1) x) := by simp only [mul_assoc, hpm, mul_one]
  have hadd (m n : ℤ)
      (hm : ∀ᵐ x ∂baseMeasure, F x * S m = S m * F (rotationIterate θ m x))
      (hn : ∀ᵐ x ∂baseMeasure, F x * S n = S n * F (rotationIterate θ n x)) :
      ∀ᵐ x ∂baseMeasure, F x * S (m+n) = S (m+n) * F (rotationIterate θ (m+n) x) := by
    filter_upwards [hm, (rotationIterate_measurePreserving θ m).quasiMeasurePreserving.ae hn]
      with x hmx hnx
    have hs : S (m+n) = S m * S n := WeightedShift.shift_add m n
    rw [hs, ← mul_assoc, hmx, mul_assoc, hnx, ← mul_assoc, ← rotationIterate_add]
  apply ae_all_iff.mpr
  intro m
  induction m using Int.induction_on with
  | zero => exact Eventually.of_forall (fun x => by simp [S])
  | succ n ih => exact hadd n 1 ih h1
  | pred n ih => simpa only [sub_eq_add_neg] using hadd (-(n : ℤ)) (-1) ih hn1

theorem IsCovariantFieldRepresentation.matrix_covariance
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) :
    ∀ m k l : ℤ, ∀ᵐ x ∂baseMeasure,
      inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) k)
        (F (rotationIterate θ m x) ((default : HilbertBasis ℤ ℂ Fiber) l)) =
      inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) (k+m))
        (F x ((default : HilbertBasis ℤ ℂ Fiber) (l+m))) := by
  apply FieldTraceCyclic.ae_matrix_covariance_of_commute
    (default : HilbertBasis ℤ ℂ Fiber) A F
    (fun m => DirectIntegral.shiftedPullback (S m)
      (rotationIterate θ m) (rotationIterate_measurePreserving θ m))
    (fun m => (WeightedShift.shift m).toLinearIsometry)
    (rotationIterate θ) (rotationIterate_measurePreserving θ)
  · exact FieldKoopman.shift_default_basis
  · exact h.2.2.2.1
  · intro m
    exact FieldTraceCyclic.shiftedPullback_ae _ _ _
  · intro m
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance
      A F (S m) (rotationIterate θ m) (rotationIterate_measurePreserving θ m) h.2.2.2.1
    filter_upwards [h.covariance_all] with x hx
    exact hx m

theorem signedShift_mem_factor (θ : ℕ → ℝ) (m : ℤ) :
    (S m).compLpL 2 baseMeasure ∈ factor θ := by
  let Q : ℤ → Hilbert →L[ℂ] Hilbert := fun k => (S k).compLpL 2 baseMeasure
  have hQadd (k l : ℤ) : Q (k+l) = Q k * Q l := WeightedShift.fieldShift_add k l
  have hQ0 : Q 0 = 1 := WeightedShift.fieldShift_zero
  have hQ1 : Q 1 ∈ factor θ := subset_vonNeumannGenerated _ (Or.inl rfl)
  have hQunit : Q 1 ∈ unitary (Hilbert →L[ℂ] Hilbert) := WeightedShift.fieldShift_mem_unitary 1
  have hQinv : Q 1 * Q (-1) = 1 := by rw [← hQadd]; norm_num [hQ0]
  have hQneg : Q (-1) = star (Q 1) := by
    calc
      Q (-1) = (star (Q 1) * Q 1) * Q (-1) := by
        rw [Unitary.star_mul_self_of_mem hQunit, one_mul]
      _ = star (Q 1) * (Q 1 * Q (-1)) := mul_assoc _ _ _
      _ = star (Q 1) := by rw [hQinv, mul_one]
  have hQn1 : Q (-1) ∈ factor θ := hQneg ▸ star_mem hQ1
  change Q m ∈ factor θ
  induction m using Int.induction_on with
  | zero => rw [hQ0]; exact one_mem _
  | succ n ih => rw [hQadd]; exact mul_mem ih hQ1
  | pred n ih =>
    rw [sub_eq_add_neg, hQadd]
    exact mul_mem ih hQn1

theorem IsCovariantFieldRepresentation.diagonal_coefficient
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r k : ℤ) :
    ∀ᵐ x ∂baseMeasure,
      inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) (k+r))
        (F x ((default : HilbertBasis ℤ ℂ Fiber) k)) =
          fieldCoefficient F r (rotationIterate θ k x) := by
  filter_upwards [h.matrix_covariance k r 0] with x hx
  simpa only [fieldCoefficient, zero_add, add_comm k r] using hx.symm

theorem IsCovariantFieldRepresentation.diagonalOperator_mem_factor
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    (S r).compLpL 2 baseMeasure *
      multiplier θ (fieldCoefficient F r) B h.1
        (h.measurable_fieldCoefficient r) (h.norm_fieldCoefficient_le r) ∈ factor θ := by
  apply mul_mem (signedShift_mem_factor θ r)
  apply subset_vonNeumannGenerated _
  exact Or.inr ⟨fieldCoefficient F r, B, h.1, h.measurable_fieldCoefficient r,
    h.norm_fieldCoefficient_le r, rfl⟩

theorem IsCovariantFieldRepresentation.diagonalOperator_ae
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) (ξ : Hilbert) :
    ((S r).compLpL 2 baseMeasure *
      multiplier θ (fieldCoefficient F r) B h.1
        (h.measurable_fieldCoefficient r) (h.norm_fieldCoefficient_le r)) ξ =ᵐ[baseMeasure]
      fun x => S r (WeightedShift.diagonal
        (multiplierField θ (fieldCoefficient F r) B (h.norm_fieldCoefficient_le r) x) (ξ x)) := by
  filter_upwards [WeightedShift.fieldShift_ae r
    (multiplier θ (fieldCoefficient F r) B h.1 (h.measurable_fieldCoefficient r)
      (h.norm_fieldCoefficient_le r) ξ),
    multiplier_ae θ (fieldCoefficient F r) B h.1 (h.measurable_fieldCoefficient r)
      (h.norm_fieldCoefficient_le r) ξ] with x hs hd
  exact hs.trans (congrArg (S r) hd)

theorem IsCovariantFieldRepresentation.diagonalOperator_basis
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) (r k : ℤ) :
    ∀ᵐ x ∂baseMeasure,
      S r (WeightedShift.diagonal
        (multiplierField θ (fieldCoefficient F r) B (h.norm_fieldCoefficient_le r) x)
          ((default : HilbertBasis ℤ ℂ Fiber) k)) =
      (inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) (k+r))
        (F x ((default : HilbertBasis ℤ ℂ Fiber) k))) •
          ((default : HilbertBasis ℤ ℂ Fiber) (k+r)) := by
  let b := (default : HilbertBasis ℤ ℂ Fiber)
  have hdiag (w : WeightedShift.Weight) : WeightedShift.diagonal w (b k) = w k • b k := by
    have hb : b k = (lp.single 2 k (1 : ℂ) : Fiber) :=
      (HilbertBasis.repr_symm_single b k).symm
    rw [hb]
    ext j
    by_cases hj : j = k <;> simp [WeightedShift.diagonal_apply, lp.single_apply, hj]
  filter_upwards [h.diagonal_coefficient r k] with x hx
  rw [hdiag, map_smul]
  change _ • WeightedShift.shift r (b k) = _
  rw [FieldKoopman.shift_default_basis]
  change fieldCoefficient F r (rotationIterate θ k x) • b (k+r) = _
  rw [← hx]

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_GaugeFourierDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Invariant233.DiagonalGauge

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem coordinate_ae (k : ℤ) (v : Lp Fiber 2 μ) :
    coordinate μ k v =ᵐ[μ] fun x => v x k :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 k).coeFn_compLpL v

theorem inclusion_ae (j : ℤ) (v : Lp ℂ 2 μ) :
    inclusion μ j v =ᵐ[μ] fun x => lp.single 2 j (v x) :=
  (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 j).coeFn_compLpL v

theorem coordinate_ext {v w : Lp Fiber 2 μ}
    (h : ∀ k : ℤ, coordinate μ k v = coordinate μ k w) : v = w := by
  have hc (k : ℤ) : ∀ᵐ x ∂μ, v x k = w x k := by
    apply (coordinate_ae μ k v).symm.trans
    rw [h k]
    exact coordinate_ae μ k w
  apply Lp.ext
  filter_upwards [MeasureTheory.ae_all_iff.mpr hc] with x hx
  exact lp.ext (funext hx)

theorem inclusion_indicatorConstLp (j : ℤ) (s : Set X)
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : ℂ) :
    inclusion μ j (indicatorConstLp 2 hs hμs c) =
      indicatorConstLp 2 hs hμs (lp.single 2 j c : Fiber) := by
  apply Lp.ext
  filter_upwards [inclusion_ae μ j (indicatorConstLp 2 hs hμs c),
    (indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs) (hμs := hμs) (c := c)),
    (indicatorConstLp_coeFn (p := 2) (μ := μ) (hs := hs) (hμs := hμs)
      (c := (lp.single 2 j c : Fiber)))] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  by_cases hx : x ∈ s <;> simp [hx]

theorem operator_ext_inclusion {A B : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ}
    (h : ∀ j : ℤ, ∀ v : Lp ℂ 2 μ, A (inclusion μ j v) = B (inclusion μ j v)) :
    A = B := by
  apply Fields.lp_operator_ext_basis_indicator
    (default : HilbertBasis ℤ ℂ Fiber) (by norm_num) A B
  intro j s hs hμs
  have hb : (default : HilbertBasis ℤ ℂ Fiber) j =
      (lp.single 2 j (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Fiber) j).symm
  rw [hb, ← inclusion_indicatorConstLp]
  exact h j _

theorem operator_ext_entries {A B : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ}
    (h : ∀ k j : ℤ, ∀ v : Lp ℂ 2 μ,
      coordinate μ k (A (inclusion μ j v)) = coordinate μ k (B (inclusion μ j v))) :
    A = B :=
  operator_ext_inclusion μ (fun j v => coordinate_ext μ (fun k => h k j v))

theorem coordinate_fieldOperator (k : ℤ) (t : Circle) (v : Lp Fiber 2 μ) :
    coordinate μ k (fieldOperator μ t v) = fourier k t • coordinate μ k v := by
  apply Lp.ext
  filter_upwards [coordinate_ae μ k (fieldOperator μ t v),
    fieldOperator_ae μ t v, coordinate_ae μ k v,
    Lp.coeFn_smul (fourier k t) (coordinate μ k v)] with x h₁ h₂ h₃ h₄
  rw [h₁, h₂, fiberOperator_apply, h₄]
  change fourier k t * v x k = fourier k t * coordinate μ k v x
  rw [h₃]

theorem fieldOperator_inclusion (j : ℤ) (t : Circle) (v : Lp ℂ 2 μ) :
    fieldOperator μ t (inclusion μ j v) = fourier j t • inclusion μ j v := by
  apply Lp.ext
  filter_upwards [fieldOperator_ae μ t (inclusion μ j v), inclusion_ae μ j v,
    Lp.coeFn_smul (fourier j t) (inclusion μ j v)] with x h₁ h₂ h₃
  rw [h₁, h₃]
  change fiberOperator t (inclusion μ j v x) = fourier j t • inclusion μ j v x
  rw [h₂]
  apply lp.ext
  funext k
  change fourier k t * (lp.single 2 j (v x) : Fiber) k =
    fourier j t * (lp.single 2 j (v x) : Fiber) k
  by_cases h : j = k
  · subst k
    rfl
  · simp [lp.single_apply, h]

theorem fourier_neg_argument (j : ℤ) (t : Circle) :
    fourier j (-t) = fourier (-j) t := by
  simp only [fourier_apply, smul_neg, neg_smul]

theorem coordinate_conjugate_inclusion
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (k j : ℤ) (t : Circle)
    (v : Lp ℂ 2 μ) :
    coordinate μ k (conjugate μ A t (inclusion μ j v)) =
      fourier (k - j) t • coordinate μ k (A (inclusion μ j v)) := by
  change coordinate μ k
    (fieldOperator μ t (A (fieldOperator μ (-t) (inclusion μ j v)))) = _
  rw [fieldOperator_inclusion]
  simp only [map_smul]
  rw [coordinate_fieldOperator, fourier_neg_argument, smul_smul]
  rw [mul_comm, ← fourier_add]
  rfl

variable [IsFiniteMeasure μ]

theorem coordinate_fourierOperator_inclusion
    (A : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ) (r k j : ℤ) (v : Lp ℂ 2 μ) :
    coordinate μ k (fourierOperator μ A r (inclusion μ j v)) =
      if k - j = r then coordinate μ k (A (inclusion μ j v)) else 0 := by
  rw [fourierOperator_apply,
    ← (coordinate μ k).integral_comp_comm (integrable_fourier_conjugate_apply μ A r _)]
  simp_rw [map_smul, coordinate_conjugate_inclusion, smul_smul, ← fourier_add]
  rw [integral_smul_const, Fejer.integral_fourier]
  have heq : -r + (k - j) = 0 ↔ k - j = r := by omega
  simp only [heq]
  split_ifs <;> simp

end Invariant233.DiagonalGauge

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductGaugeFourier
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.hilbert_separable _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

variable {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
  {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}

theorem IsCovariantFieldRepresentation.matrixDiagonal_mem_factor
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    h.matrixDiagonal r ∈ factor θ := h.diagonalOperator_mem_factor r

private theorem single_eq_smul_basis (j : ℤ) (c : ℂ) :
    (lp.single 2 j c : Fiber) = c • (default : HilbertBasis ℤ ℂ Fiber) j := by
  have hb : (default : HilbertBasis ℤ ℂ Fiber) j =
      (lp.single 2 j (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single (default : HilbertBasis ℤ ℂ Fiber) j).symm
  rw [hb]
  simpa only [smul_eq_mul, mul_one] using
    (lp.single_smul (E := fun _ : ℤ => ℂ) 2 j c (1 : ℂ))

private theorem inner_basis_coordinate (j : ℤ) (v : Fiber) :
    inner ℂ ((default : HilbertBasis ℤ ℂ Fiber) j) v = v j :=
  ((default : HilbertBasis ℤ ℂ Fiber).repr_apply_apply v j).symm

theorem IsCovariantFieldRepresentation.coordinate_matrixDiagonal_inclusion
    (h : IsCovariantFieldRepresentation θ A F B) (r k j : ℤ)
    (v : Lp ℂ 2 baseMeasure) :
    DiagonalGauge.coordinate baseMeasure k
        (h.matrixDiagonal r (DiagonalGauge.inclusion baseMeasure j v)) =
      if k - j = r then DiagonalGauge.coordinate baseMeasure k
        (A (DiagonalGauge.inclusion baseMeasure j v)) else 0 := by
  let b := (default : HilbertBasis ℤ ℂ Fiber)
  have hb0 (n : ℤ) : b n = (lp.single 2 n (1 : ℂ) : Fiber) :=
    (HilbertBasis.repr_symm_single b n).symm
  have hdiag := h.diagonalOperator_ae r (DiagonalGauge.inclusion baseMeasure j v)
  change h.matrixDiagonal r (DiagonalGauge.inclusion baseMeasure j v) =ᵐ[baseMeasure] _ at hdiag
  by_cases hkj : k - j = r
  · rw [ite_eq_left hkj]
    have hk : k = j + r := by omega
    subst k
    apply Lp.ext
    filter_upwards [DiagonalGauge.coordinate_ae baseMeasure (j+r)
        (h.matrixDiagonal r (DiagonalGauge.inclusion baseMeasure j v)),
      hdiag, DiagonalGauge.inclusion_ae baseMeasure j v,
      h.diagonalOperator_basis r j,
      DiagonalGauge.coordinate_ae baseMeasure (j+r)
        (A (DiagonalGauge.inclusion baseMeasure j v)),
      h.2.2.2.1 (DiagonalGauge.inclusion baseMeasure j v)] with x hc hd hi hb hcA hA
    rw [hc, hd, hi, single_eq_smul_basis, map_smul, map_smul, hb,
      hcA, hA, hi, single_eq_smul_basis, map_smul]
    change v x * (inner ℂ (b (j+r)) (F x (b j)) * b (j+r) (j+r)) =
      v x * (F x (b j)) (j+r)
    rw [inner_basis_coordinate]
    have hbb : b (j+r) (j+r) = 1 := by
      rw [hb0]
      simp
    rw [hbb, mul_one]
  · rw [ite_eq_right hkj]
    apply Lp.ext
    filter_upwards [DiagonalGauge.coordinate_ae baseMeasure k
        (h.matrixDiagonal r (DiagonalGauge.inclusion baseMeasure j v)),
      hdiag, DiagonalGauge.inclusion_ae baseMeasure j v,
      h.diagonalOperator_basis r j,
      Lp.coeFn_zero ℂ 2 baseMeasure] with x hc hd hi hb hz
    rw [hc, hd, hi, single_eq_smul_basis, map_smul, map_smul, hb, hz]
    change v x * (inner ℂ (b (j+r)) (F x (b j)) * b (j+r) k) = 0
    have hbb : b (j+r) k = 0 := by
      rw [hb0]
      have hk : j+r ≠ k := by omega
      simp [lp.single_apply, hk]
    rw [hbb, mul_zero, mul_zero]

theorem IsCovariantFieldRepresentation.fourierOperator_eq_matrixDiagonal
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) :
    DiagonalGauge.fourierOperator baseMeasure A r = h.matrixDiagonal r := by
  apply DiagonalGauge.operator_ext_entries baseMeasure
  intro k j v
  rw [DiagonalGauge.coordinate_fourierOperator_inclusion,
    h.coordinate_matrixDiagonal_inclusion]

theorem IsCovariantFieldRepresentation.matrixDiagonal_neg_apply_integral
    (h : IsCovariantFieldRepresentation θ A F B) (r : ℤ) (v : Hilbert) :
    h.matrixDiagonal (-r) v = ∫ t : DiagonalGauge.Circle,
      fourier r t • DiagonalGauge.conjugate baseMeasure A t v
        ∂AddCircle.haarAddCircle := by
  rw [← h.fourierOperator_eq_matrixDiagonal, DiagonalGauge.fourierOperator_apply]
  simp only [neg_neg]

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductFieldConverse
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.hilbert_separable _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.ProductModel

theorem IsCovariantFieldRepresentation.mem_factor
    {θ : ℕ → ℝ} {A : Hilbert →L[ℂ] Hilbert}
    {F : Base → Fiber →L[ℂ] Fiber} {B : ℝ}
    (h : IsCovariantFieldRepresentation θ A F B) : A ∈ factor θ := by
  have hm := StrongFourierRecovery.mem_of_fourier_modes (factor θ)
    (DiagonalGauge.conjugate baseMeasure A)
    (DiagonalGauge.continuous_conjugate_apply baseMeasure A)
    (fun r => h.matrixDiagonal (-r))
    h.matrixDiagonal_neg_apply_integral
    (fun r => h.matrixDiagonal_mem_factor (-r))
  simpa only [DiagonalGauge.conjugate_zero] using hm

theorem mem_factor_iff_covariantFieldRepresentation (θ : ℕ → ℝ)
    (A : Hilbert →L[ℂ] Hilbert) :
    A ∈ factor θ ↔ ∃ (F : Base → Fiber →L[ℂ] Fiber) (B : ℝ),
      IsCovariantFieldRepresentation θ A F B := by
  constructor
  · intro hA
    obtain ⟨F, hF⟩ := exists_covariantFieldRepresentation hA
    exact ⟨F, ‖A‖, hF⟩
  · rintro ⟨F, B, hF⟩
    exact hF.mem_factor

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductFactorComplete
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.ProductModel

theorem factor_complete_oai (θ : ℕ → ℝ)
    (hθ : ProductModel.JointlyRationallyIndependent θ) :
    IsTypeII1FactorWithVector (ProductModel.factor θ) ProductModel.traceVector ∧
      HasSeparablePredual (ProductModel.factor θ) ∧
      (∀ A : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert,
        A ∈ ProductModel.factor θ ↔
          ∃ (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber)
            (B : ℝ), ProductModel.IsCovariantFieldRepresentation θ A F B) ∧
      (∀ (A : ProductModel.Hilbert →L[ℂ] ProductModel.Hilbert)
        (F : ProductModel.Base → ProductModel.Fiber →L[ℂ] ProductModel.Fiber) (B : ℝ),
        ProductModel.IsCovariantFieldRepresentation θ A F B →
          vectorTrace ProductModel.traceVector A = ProductModel.centralDiagonalIntegral F) := by
  refine ⟨factor_isTypeII1FactorWithVector θ hθ,
    factor_hasSeparablePredual θ,
    mem_factor_iff_covariantFieldRepresentation θ, ?_⟩
  intro A F B h
  exact h.vectorTrace_eq

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.factor_complete_oai := @OAI.Invariant233.ProductModel.factor_complete_oai
