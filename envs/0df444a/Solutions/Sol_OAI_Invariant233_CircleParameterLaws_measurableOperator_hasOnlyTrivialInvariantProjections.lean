-- Prove2me | solution 1 for OAI.Invariant233.CircleParameterLaws.measurableOperator_hasOnlyTrivialInvariantProjections
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:32:15.243813+00:00
-- url     : https://prove2.me/submissions/a6c571c7-e72c-4216-9b82-3ea582e26257

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_CircleCoupling_endpoint_absolutelyContinuous
import Theorems.Thm_OAI_Invariant233_CircleCoupling_orderedCouplingIdentities_of_rational
import Theorems.Thm_OAI_Invariant233_CircleCoupling_tail_exceptional_families_of_subset
import Theorems.Thm_OAI_Invariant233_CircleParameterLaws_exists_rational_graph_field_with_truncation_mass
import Theorems.Thm_OAI_Invariant233_CircleParameterLaws_rational_graphs_of_representation

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConvolutionContradiction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ConvolutionContradiction

theorem sqrt_exp_attenuation (L : ℝ) :
    Real.sqrt (Real.exp (-L / 400)) = Real.exp (-L / 800) := by
  rw [← Real.exp_half]
  congr 1
  ring

theorem tail_attenuation_le (L : ℝ) (hL : 0 ≤ L) :
    Real.exp (-L) + 2 * Real.sqrt (Real.exp (-L / 400)) ≤
      3 * Real.exp (-L / 10000) := by
  rw [sqrt_exp_attenuation]
  have h₁ : Real.exp (-L) ≤ Real.exp (-L / 10000) :=
    Real.exp_le_exp.mpr (by linarith)
  have h₂ : Real.exp (-L / 800) ≤ Real.exp (-L / 10000) :=
    Real.exp_le_exp.mpr (by linarith)
  linarith

theorem coefficient_tail_le (K : ℕ) (L ε j : ℝ) (hL : 0 ≤ L)
    (hchoice : (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000) ≤ ε / j) :
    (2 * (K : ℝ) + 1) *
      (Real.exp (-L) + 2 * Real.sqrt (Real.exp (-L / 400))) ≤ ε / j := by
  calc
    _ ≤ (2 * (K : ℝ) + 1) * (3 * Real.exp (-L / 10000)) :=
      mul_le_mul_of_nonneg_left (tail_attenuation_le L hL) (by positivity)
    _ = (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000) := by ring
    _ ≤ ε / j := hchoice

theorem fixed_stage_contradiction (c ε j : ℝ) (hε : 0 < ε)
    (hstage : 1 / j < c) (hbound : c * ε ≤ ε / j) : False := by
  have hstrict : ε / j < c * ε := by
    calc
      ε / j = (1 / j) * ε := by ring
      _ < c * ε := mul_lt_mul_of_pos_right hstage hε
  exact (not_lt_of_ge hbound) hstrict

end Invariant233.ConvolutionContradiction

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConvolutionRatios
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ComplexConjugate ENNReal lp

namespace InvariantProjection

theorem l2_reindexed_absolute_products (ξ γ : ℓ²(ℤ, ℂ)) (e : ℤ ≃ ℤ) :
    (Summable fun v : ℤ => ‖ξ v‖ * ‖γ (e v)‖) ∧
      (∑' v : ℤ, ‖ξ v‖ * ‖γ (e v)‖) ≤ ‖ξ‖ * ‖γ‖ := by
  let γe : ℓ²(ℤ, ℂ) := ⟨fun v => γ (e v), by
    apply memℓp_gen
    exact e.summable_iff.mpr ((lp.memℓp γ).summable (by norm_num))⟩
  have hnorm : ‖γe‖ = ‖γ‖ := by
    rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
    congr 1
    exact e.tsum_eq (fun v => ‖γ v‖ ^ (2 : ℝ≥0∞).toReal)
  simpa only [hnorm] using lp.tsum_mul_le_mul_norm
    (p := 2) (q := 2) (by simpa using Real.HolderConjugate.two_two) ξ γe

theorem l2_reindexed_multiplier_bound (ξ γ : ℓ²(ℤ, ℂ)) (e : ℤ ≃ ℤ)
    (r : ℤ → ℝ) (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1) :
    (Summable fun v : ℤ => ‖(r v : ℂ) * ξ v * conj (γ (e v))‖) ∧
      (∑' v : ℤ, ‖(r v : ℂ) * ξ v * conj (γ (e v))‖) ≤ ‖ξ‖ * ‖γ‖ := by
  have hbase := l2_reindexed_absolute_products ξ γ e
  have hbound (v : ℤ) :
      ‖(r v : ℂ) * ξ v * conj (γ (e v))‖ ≤ ‖ξ v‖ * ‖γ (e v)‖ := by
    simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hr v).1]
    calc
      r v * ‖ξ v‖ * ‖γ (e v)‖ ≤ 1 * ‖ξ v‖ * ‖γ (e v)‖ := by gcongr; exact (hr v).2
      _ = _ := by ring
  have hs := Summable.of_nonneg_of_le (fun v => norm_nonneg _) hbound hbase.1
  exact ⟨hs, (Summable.tsum_le_tsum hbound hs hbase.1).trans hbase.2⟩

theorem convolution_coefficient_factorization
    (Fx Fy : ℤ → ℝ) (ξ γ : ℤ → ℂ) (n v : ℤ) :
    (ξ v / (Fx v : ℂ)) * ((Fy (n + v) : ℂ) * conj (γ (n + v))) =
      ((Fy (n + v) / Fx v : ℝ) : ℂ) * ξ v * conj (γ (n + v)) := by
  push_cast
  ring

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteConvolutionMeasurability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.FiniteWindow

open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_convolution (K n : ℕ) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i)) :
    Measurable (fun ω => convolution K (a ω) (b ω) n) := by
  unfold convolution
  fun_prop

theorem norm_convolution_le (K n : ℕ) (D : ℝ) (a b : ℤ → ℂ)
    (ha : ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D)
    (hb : ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) :
    ‖convolution K a b n‖ ≤ (2 * K + 1 : ℕ) * D ^ 2 := by
  classical
  have hD : 0 ≤ D := (norm_nonneg (a 0)).trans (ha 0 (by simp))
  unfold convolution
  calc
    ‖∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
        (fun i => |(n : ℤ) + i| ≤ (K : ℤ)), a i * b (-(n : ℤ) - i)‖
        ≤ ∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
          (fun i => |(n : ℤ) + i| ≤ (K : ℤ)), ‖a i * b (-(n : ℤ) - i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ (Finset.Icc (-(K : ℤ)) (K : ℤ)).filter
          (fun i => |(n : ℤ) + i| ≤ (K : ℤ)), D ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hin⟩ := Finset.mem_filter.mp hi
      have hiK : |i| ≤ (K : ℤ) := abs_le.mpr (Finset.mem_Icc.mp his)
      have hniK : |-(n : ℤ) - i| ≤ (K : ℤ) := by
        simpa only [show -(n : ℤ) - i = -((n : ℤ) + i) by omega, abs_neg] using hin
      rw [norm_mul, pow_two]
      exact mul_le_mul (ha i hiK) (hb _ hniK) (norm_nonneg _) hD
    _ ≤ ∑ i ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), D ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i hi hnot => sq_nonneg D)
    _ = (2 * K + 1 : ℕ) * D ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
      congr 2
      omega

theorem integrableOn_convolution (μ : Measure Ω) (E : Set Ω)
    (hE : μ E < ∞) (K n : ℕ) (D : ℝ) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i))
    (haD : ∀ᵐ ω ∂μ.restrict E, ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D)
    (hbD : ∀ᵐ ω ∂μ.restrict E, ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) :
    IntegrableOn (fun ω => convolution K (a ω) (b ω) n) E μ := by
  apply IntegrableOn.of_bound hE (measurable_convolution K n a b ha hb).aestronglyMeasurable
    ((2 * K + 1 : ℕ) * D ^ 2)
  filter_upwards [haD, hbD] with ω hωa hωb
  exact norm_convolution_le K n D (a ω) (b ω) hωa hωb

theorem integrableOn_norm_convolution (μ : Measure Ω) (E : Set Ω)
    (hE : μ E < ∞) (K n : ℕ) (D : ℝ) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i))
    (haD : ∀ᵐ ω ∂μ.restrict E, ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D)
    (hbD : ∀ᵐ ω ∂μ.restrict E, ∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) :
    IntegrableOn (fun ω => ‖convolution K (a ω) (b ω) n‖) E μ :=
  (integrableOn_convolution μ E hE K n D a b ha hb haD hbD).norm

end Invariant233.FiniteWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_LaurentNoncancellation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Invariant233.FiniteWindow

open Invariant233.LaurentWindow
open InvariantProjection.FiniteConvolution

theorem support_laurent_coeff_subset (K : ℕ) (a : ℤ → ℂ) :
    Function.support (laurent K a).coeff ⊆ Set.Icc (-(K : ℤ)) (K : ℤ) := by
  intro i hi
  have hne := Function.mem_support.mp hi
  by_contra h
  have habs : ¬ |i| ≤ (K : ℤ) := by simpa only [abs_le, Set.mem_Icc] using h
  exact hne (by simp only [laurent_coeff, ite_eq_right habs])

theorem sum_laurent_coeff_eq_convolution (K : ℕ) (a b : ℤ → ℂ) (n : ℕ) :
    (∑ v ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
      (laurent K a).coeff v * (laurent K b).coeff (-(n : ℤ) - v)) =
      convolution K a b n := by
  classical
  unfold convolution
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  have hvabs : |v| ≤ (K : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hv)
  have hneg : |-(n : ℤ) - v| = |(n : ℤ) + v| := by
    rw [show -(n : ℤ) - v = -((n : ℤ) + v) by ring, abs_neg]
  rw [laurent_coeff, ite_eq_left hvabs, laurent_coeff, hneg]
  split_ifs <;> simp

theorem convolution_sum_lower_bound_of_supported_bound (K : ℕ) (D δ ε : ℝ)
    (hsource : ∀ A B : ℤ → ℂ,
      Function.support A ⊆ Set.Icc (-(K : ℤ)) (K : ℤ) →
      Function.support B ⊆ Set.Icc (-(K : ℤ)) (K : ℤ) →
      (∀ i, ‖A i‖ ≤ D) → (∀ i, ‖B i‖ ≤ D) →
      δ ≤ ‖A 0‖ → δ ≤ ‖B 0‖ →
      ∃ n ∈ Finset.Icc 0 (2 * K), ε ≤ ‖∑ v ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
        A v * B (-(n : ℤ) - v)‖) :
    ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖convolution K a b n‖ := by
  intro a b ha hb ha0 hb0
  have hD : 0 ≤ D := (norm_nonneg (a 0)).trans (ha 0 (by simp))
  have coeff_bound : ∀ c : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖c i‖ ≤ D) →
      ∀ i, ‖(laurent K c).coeff i‖ ≤ D := by
    intro c hc i
    rw [laurent_coeff]
    split_ifs with hi
    · exact hc i hi
    · simpa only [norm_zero] using hD
  obtain ⟨n, hn, hc⟩ := hsource (laurent K a).coeff (laurent K b).coeff
    (support_laurent_coeff_subset K a) (support_laurent_coeff_subset K b)
    (coeff_bound a ha) (coeff_bound b hb)
    (by simpa only [laurent_coeff_zero] using ha0)
    (by simpa only [laurent_coeff_zero] using hb0)
  rw [sum_laurent_coeff_eq_convolution] at hc
  exact hc.trans (Finset.single_le_sum (fun k hk => norm_nonneg _)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)))

end Invariant233.FiniteWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_FiniteWindowIntegralLower
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Invariant233.FiniteWindow

theorem integrableOn_convolution_sum
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℕ) (D : ℝ) (E : Set Ω) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i))
    (hE : ∀ᵐ ω ∂μ.restrict E,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D) ∧
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D)) :
    IntegrableOn (fun ω => ∑ n ∈ Finset.range (2 * K + 1),
      ‖convolution K (a ω) (b ω) n‖) E μ := by
  classical
  exact integrable_finsetSum _ (fun n _ =>
    integrableOn_norm_convolution μ E (measure_lt_top μ E) K n D a b ha hb
      (hE.mono (fun _ h => h.1)) (hE.mono (fun _ h => h.2)))

theorem integral_lower_of_sum_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (K : ℕ) (D δ ε : ℝ)
    (hcoeff : ∀ a b : ℤ → ℂ,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a i‖ ≤ D) →
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b i‖ ≤ D) →
      δ ≤ ‖a 0‖ → δ ≤ ‖b 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖convolution K a b n‖)
    (E : Set Ω) (a b : Ω → ℤ → ℂ)
    (ha : ∀ i, Measurable (fun ω => a ω i))
    (hb : ∀ i, Measurable (fun ω => b ω i))
    (hE : ∀ᵐ ω ∂μ.restrict E,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D) ∧
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) ∧
      δ ≤ ‖a ω 0‖ ∧ δ ≤ ‖b ω 0‖) :
    ε * μ.real E ≤ ∫ ω in E, ∑ n ∈ Finset.range (2 * K + 1),
      ‖convolution K (a ω) (b ω) n‖ ∂μ := by
  have hbounds : ∀ᵐ ω ∂μ.restrict E,
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖a ω i‖ ≤ D) ∧
      (∀ i : ℤ, |i| ≤ (K : ℤ) → ‖b ω i‖ ≤ D) :=
    hE.mono (fun _ h => ⟨h.1, h.2.1⟩)
  have hi := integrableOn_convolution_sum μ K D E a b ha hb hbounds
  have hpoint : ∀ᵐ ω ∂μ.restrict E,
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖convolution K (a ω) (b ω) n‖ :=
    hE.mono (fun ω h => hcoeff (a ω) (b ω) h.1 h.2.1 h.2.2.1 h.2.2.2)
  have h := integral_mono_ae (integrable_const ε) hi hpoint
  simpa only [setIntegral_const, smul_eq_mul, mul_comm] using h

theorem finite_sum_obstruction
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Set Ω) (N : ℕ) (F : ℕ → Ω → ℝ) (c ε C : ℝ)
    (hε : 0 ≤ ε) (hmass : c ≤ μ.real E)
    (hint : ∀ n ∈ Finset.range N, IntegrableOn (F n) E μ)
    (hlower : ε * μ.real E ≤ ∫ ω in E, ∑ n ∈ Finset.range N, F n ω ∂μ)
    (hupper : ∀ n ∈ Finset.range N, (∫ ω in E, F n ω ∂μ) ≤ C) :
    c * ε ≤ (N : ℝ) * C := by
  calc
    c * ε ≤ ε * μ.real E := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_right hmass hε
    _ ≤ ∫ ω in E, ∑ n ∈ Finset.range N, F n ω ∂μ := hlower
    _ = ∑ n ∈ Finset.range N, ∫ ω in E, F n ω ∂μ :=
      integral_finsetSum _ hint
    _ ≤ ∑ n ∈ Finset.range N, C := Finset.sum_le_sum hupper
    _ = (N : ℝ) * C := by simp [nsmul_eq_mul]

end Invariant233.FiniteWindow

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_MaskedCauchySchwarz
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace InvariantProjection

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem integral_indicator_le_of_condExp_indicator_le
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [IsFiniteMeasure μ] {H : Set Ω} (hH : MeasurableSet[mΩ] H)
    {w : Ω → ℝ} {δ : ℝ} (hw : Integrable w μ)
    (hwm : StronglyMeasurable[m] w) (hw_nonneg : 0 ≤ᵐ[μ] w)
    (hcond : μ[H.indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ) :
    (∫ ω, H.indicator w ω ∂μ) ≤ δ * ∫ ω, w ω ∂μ := by
  have hmul : w * H.indicator (fun _ => (1 : ℝ)) = H.indicator w := by
    funext ω
    by_cases hω : ω ∈ H <;> simp [hω]
  have hpull := condExp_mul_of_stronglyMeasurable_left hwm
    (show Integrable (w * H.indicator (fun _ => (1 : ℝ))) μ by
      rw [hmul]
      exact hw.indicator hH)
    ((integrable_const (1 : ℝ)).indicator hH)
  have hprod : Integrable (w * μ[H.indicator (fun _ => (1 : ℝ)) | m]) μ :=
    integrable_condExp.congr hpull
  calc
    (∫ ω, H.indicator w ω ∂μ) =
        ∫ ω, μ[w * H.indicator (fun _ => (1 : ℝ)) | m] ω ∂μ := by
      rw [integral_condExp hm, hmul]
    _ = ∫ ω, w ω * μ[H.indicator (fun _ => (1 : ℝ)) | m] ω ∂μ :=
      integral_congr_ae hpull
    _ ≤ ∫ ω, δ * w ω ∂μ := by
      apply integral_mono_ae hprod (hw.const_mul δ)
      filter_upwards [hcond, hw_nonneg] with ω hω hwω
      simpa only [Pi.mul_apply, mul_comm] using mul_le_mul_of_nonneg_left hω hwω
    _ = δ * ∫ ω, w ω ∂μ := integral_const_mul δ w

theorem lintegral_tsum_indicator_le_of_condExp_indicator_le
    {ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [IsFiniteMeasure μ] {H : ι → Set Ω} (hH : ∀ i, MeasurableSet[mΩ] (H i))
    {w : ι → Ω → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i, Integrable (w i) μ)
    (hwm : ∀ i, StronglyMeasurable[m] (w i))
    (hw_nonneg : ∀ i, 0 ≤ᵐ[μ] w i)
    (hcond : ∀ i, μ[(H i).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal ((H i).indicator (w i) ω) ∂μ) ≤
      ENNReal.ofReal δ * ∫⁻ ω, ∑' i, ENNReal.ofReal (w i ω) ∂μ := by
  rw [lintegral_tsum (fun i => ((hw i).indicator (hH i)).aemeasurable.ennreal_ofReal),
    lintegral_tsum (fun i => (hw i).aemeasurable.ennreal_ofReal),
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro i
  have hmask_nonneg : 0 ≤ᵐ[μ] (H i).indicator (w i) := by
    filter_upwards [hw_nonneg i] with ω hω
    by_cases hi : ω ∈ H i
    · simpa only [Set.indicator_of_mem hi, Pi.zero_apply] using hω
    · simp [hi]
  rw [← ofReal_integral_eq_lintegral_ofReal ((hw i).indicator (hH i)) hmask_nonneg,
    ← ofReal_integral_eq_lintegral_ofReal (hw i) (hw_nonneg i),
    ← ENNReal.ofReal_mul hδ]
  exact ENNReal.ofReal_le_ofReal
    (integral_indicator_le_of_condExp_indicator_le (mΩ := mΩ) hm (hH i) (hw i) (hwm i)
      (hw_nonneg i) (hcond i))

theorem lintegral_tsum_indicator_le_of_condExp_indicator_le_of_energy_le_one
    {ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    [IsFiniteMeasure μ] {H : ι → Set Ω} (hH : ∀ i, MeasurableSet[mΩ] (H i))
    {w : ι → Ω → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : ∀ i, Integrable (w i) μ)
    (hwm : ∀ i, StronglyMeasurable[m] (w i))
    (hw_nonneg : ∀ i, 0 ≤ᵐ[μ] w i)
    (hcond : ∀ i, μ[(H i).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ)
    (henergy : (∫⁻ ω, ∑' i, ENNReal.ofReal (w i ω) ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, ENNReal.ofReal ((H i).indicator (w i) ω) ∂μ) ≤
      ENNReal.ofReal δ := by
  calc
    _ ≤ ENNReal.ofReal δ * ∫⁻ ω, ∑' i, ENNReal.ofReal (w i ω) ∂μ :=
      lintegral_tsum_indicator_le_of_condExp_indicator_le (mΩ := mΩ) hm hH hδ hw hwm hw_nonneg hcond
    _ ≤ ENNReal.ofReal δ * 1 := mul_le_mul_right henergy _
    _ = ENNReal.ofReal δ := mul_one _

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_MaskedConvolutionTail
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection

theorem norm_finset_sum_le_complement
    {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (hc : Summable fun i => ‖c i‖) (hz : (∑' i, c i) = 0) :
    ‖∑ i ∈ s, c i‖ ≤ ∑' i : ↑((s : Set ι)ᶜ), ‖c i‖ := by
  have hsplit := hc.of_norm.sum_add_tsum_compl (s := s)
  rw [hz] at hsplit
  have heq : (∑ i ∈ s, c i) = -(∑' i : ↑((s : Set ι)ᶜ), c i) := by
    simpa using eq_neg_of_add_eq_zero_left hsplit
  rw [heq, norm_neg]
  exact norm_tsum_le_tsum_norm (hc.subtype fun i => i ∈ (s : Set ι)ᶜ)

theorem norm_finset_sum_le_two_tails
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w e₁ e₂ : ι → ℝ) (η : ℝ)
    (hc : Summable fun i => ‖c i‖) (hz : (∑' i, c i) = 0)
    (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i) (hη : 0 ≤ η)
    (h₁ : ∀ i, 0 ≤ e₁ i ∧ e₁ i ≤ w i) (h₂ : ∀ i, 0 ≤ e₂ i ∧ e₂ i ≤ w i)
    (hb : ∀ i, i ∉ s → ‖c i‖ ≤ η * w i + e₁ i + e₂ i) :
    ‖∑ i ∈ s, c i‖ ≤ η * (∑' i, w i) +
      (∑' i : ↑((s : Set ι)ᶜ), e₁ i) + (∑' i : ↑((s : Set ι)ᶜ), e₂ i) := by
  have hs₁ : Summable e₁ := Summable.of_nonneg_of_le
    (fun i => (h₁ i).1) (fun i => (h₁ i).2) hw
  have hs₂ : Summable e₂ := Summable.of_nonneg_of_le
    (fun i => (h₂ i).1) (fun i => (h₂ i).2) hw
  have hwc := hw.subtype (fun i => i ∈ (s : Set ι)ᶜ)
  have h₁c := hs₁.subtype (fun i => i ∈ (s : Set ι)ᶜ)
  have h₂c := hs₂.subtype (fun i => i ∈ (s : Set ι)ᶜ)
  have hct := hc.subtype (fun i => i ∈ (s : Set ι)ᶜ)
  simp only [Function.comp_def] at hwc h₁c h₂c hct
  have htail : (∑' i : ↑((s : Set ι)ᶜ), ‖c i‖) ≤
      ∑' i : ↑((s : Set ι)ᶜ), (η * w i + e₁ i + e₂ i) :=
    Summable.tsum_le_tsum (fun i => hb i i.property) hct
      (((hwc.mul_left η).add h₁c).add h₂c)
  have hwle : (∑' i : ↑((s : Set ι)ᶜ), w i) ≤ ∑' i, w i := by
    have hsplit := hw.sum_add_tsum_compl (s := s)
    have hsum : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg fun i hi => hw0 i
    simpa using (le_add_of_nonneg_left hsum).trans_eq hsplit
  calc
    ‖∑ i ∈ s, c i‖ ≤ ∑' i : ↑((s : Set ι)ᶜ), ‖c i‖ :=
      norm_finset_sum_le_complement s c hc hz
    _ ≤ ∑' i : ↑((s : Set ι)ᶜ), (η * w i + e₁ i + e₂ i) := htail
    _ = η * (∑' i : ↑((s : Set ι)ᶜ), w i) +
        (∑' i : ↑((s : Set ι)ᶜ), e₁ i) + (∑' i : ↑((s : Set ι)ᶜ), e₂ i) := by
      rw [((hwc.mul_left η).add h₁c).tsum_add h₂c, (hwc.mul_left η).tsum_add h₁c,
        tsum_mul_left]
    _ ≤ η * (∑' i, w i) +
        (∑' i : ↑((s : Set ι)ᶜ), e₁ i) + (∑' i : ↑((s : Set ι)ᶜ), e₂ i) := by
      gcongr

theorem norm_finset_sum_le_masked_tail
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (w : ι → ℝ) (η : ℝ)
    (H₁ H₂ : Set ι)
    (hc : Summable fun i => ‖c i‖) (hz : (∑' i, c i) = 0)
    (hw : Summable w) (hw0 : ∀ i, 0 ≤ w i) (hη : 0 ≤ η)
    (hb : ∀ i, i ∉ s → ‖c i‖ ≤
      (η + H₁.indicator (fun _ => (1 : ℝ)) i +
        H₂.indicator (fun _ => (1 : ℝ)) i) * w i) :
    ‖∑ i ∈ s, c i‖ ≤ η * (∑' i, w i) +
      (∑' i : ↑((s : Set ι)ᶜ), H₁.indicator w i) +
      (∑' i : ↑((s : Set ι)ᶜ), H₂.indicator w i) := by
  classical
  apply norm_finset_sum_le_two_tails s c w (H₁.indicator w) (H₂.indicator w)
    η hc hz hw hw0 hη
  · intro i
    by_cases hi : i ∈ H₁ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hw0 i]
  · intro i
    by_cases hi : i ∈ H₂ <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hw0 i]
  · intro i hi
    convert hb i hi using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Set.indicator_apply]
    split_ifs <;> ring

theorem omitted_index_selector (K n v : ℤ)
    (h : ¬ (|v| ≤ K ∧ |n + v| ≤ K)) :
    K < |if K < |v| then v else n + v| := by
  split_ifs with hv
  · exact hv
  · have hv' : |v| ≤ K := le_of_not_gt hv
    exact lt_of_not_ge (fun hn => h ⟨hv', hn⟩)

theorem omitted_index_ratio_bound (K n v : ℤ) (R : ℤ → ℝ) (r : ℝ)
    (hr : r ≤ min (R v) (R (n + v))) :
    r ≤ R (if K < |v| then v else n + v) := by
  split_ifs
  · exact hr.trans (min_le_left _ _)
  · exact hr.trans (min_le_right _ _)

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_MaskedTail
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace Invariant233.MaskedTail

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_mul_le_sqrt
    {a b : Ω → ℝ≥0∞} {δ : ℝ≥0∞}
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (ha2 : (∫⁻ ω, a ω ^ (2 : ℕ) ∂μ) ≤ δ)
    (hb2 : (∫⁻ ω, b ω ^ (2 : ℕ) ∂μ) ≤ 1) :
    (∫⁻ ω, a ω * b ω ∂μ) ≤ δ ^ (1 / 2 : ℝ) := by
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj ha hb
  simp only [Pi.mul_apply, ENNReal.rpow_two] at hcs
  calc
    (∫⁻ ω, a ω * b ω ∂μ) ≤
        (∫⁻ ω, a ω ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫⁻ ω, b ω ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := hcs
    _ ≤ δ ^ (1 / 2 : ℝ) * (1 : ℝ≥0∞) ^ (1 / 2 : ℝ) :=
      mul_le_mul' (ENNReal.rpow_le_rpow ha2 (by norm_num))
        (ENNReal.rpow_le_rpow hb2 (by norm_num))
    _ = δ ^ (1 / 2 : ℝ) := by simp

theorem lintegral_indicator_mul_le_sqrt
    {a b : Ω → ℝ≥0∞} {δ : ℝ≥0∞} {H : Set Ω}
    (hH : MeasurableSet H)
    (ha : AEMeasurable a μ) (hb : AEMeasurable b μ)
    (ha2 : (∫⁻ ω, H.indicator (fun ω => a ω ^ (2 : ℕ)) ω ∂μ) ≤ δ)
    (hb2 : (∫⁻ ω, b ω ^ (2 : ℕ) ∂μ) ≤ 1) :
    (∫⁻ ω, H.indicator (fun ω => a ω * b ω) ω ∂μ) ≤
      δ ^ (1 / 2 : ℝ) := by
  have hpow : (fun ω => (H.indicator a ω) ^ (2 : ℕ)) =
      H.indicator (fun ω => a ω ^ (2 : ℕ)) := by
    funext ω
    by_cases hω : ω ∈ H <;> simp [hω]
  have hmul : (fun ω => H.indicator a ω * b ω) =
      H.indicator (fun ω => a ω * b ω) := by
    funext ω
    by_cases hω : ω ∈ H <;> simp [hω]
  have h := lintegral_mul_le_sqrt (ha.indicator hH) hb (by simpa [hpow] using ha2) hb2
  simpa [hmul] using h

theorem lintegral_tsum_indicator_mul_le_sqrt
    {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    {a b : Ω × ι → ℝ≥0∞} {δ : ℝ≥0∞} {H : Set (Ω × ι)}
    (hH : MeasurableSet H)
    (ha : AEMeasurable a (μ.prod Measure.count))
    (hb : AEMeasurable b (μ.prod Measure.count))
    (ha2 : (∫⁻ ω, ∑' i, H.indicator (fun z => a z ^ (2 : ℕ)) (ω, i) ∂μ) ≤ δ)
    (hb2 : (∫⁻ ω, ∑' i, b (ω, i) ^ (2 : ℕ) ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, H.indicator (fun z => a z * b z) (ω, i) ∂μ) ≤
      δ ^ (1 / 2 : ℝ) := by
  have ha2' : (∫⁻ z, H.indicator (fun z => a z ^ (2 : ℕ)) z
      ∂μ.prod Measure.count) ≤ δ := by
    rw [lintegral_prod _ ((ha.pow_const 2).indicator hH)]
    simpa only [lintegral_count] using ha2
  have hb2' : (∫⁻ z, b z ^ (2 : ℕ) ∂μ.prod Measure.count) ≤ 1 := by
    rw [lintegral_prod _ (hb.pow_const 2)]
    simpa only [lintegral_count] using hb2
  have h := lintegral_indicator_mul_le_sqrt hH ha hb ha2' hb2'
  change (∫⁻ z, H.indicator (a * b) z ∂μ.prod Measure.count) ≤ _ at h
  rw [lintegral_prod _ ((ha.mul hb).indicator hH)] at h
  simpa only [lintegral_count, Pi.mul_def] using h

theorem real_tsum_integrable_of_lintegral_bound
    {ι : Type*} [Countable ι] {f : ι → Ω → ℝ} {C : ℝ}
    (hf : ∀ i, Measurable (f i)) (hf_nonneg : ∀ i ω, 0 ≤ f i ω)
    (hC : 0 ≤ C)
    (hbound : (∫⁻ ω, ∑' i, ENNReal.ofReal (f i ω) ∂μ) ≤ ENNReal.ofReal C) :
    (∀ᵐ ω ∂μ, Summable (fun i => f i ω)) ∧
      Integrable (fun ω => ∑' i, f i ω) μ ∧
      (∫ ω, ∑' i, f i ω ∂μ) ≤ C := by
  have hsum_meas : Measurable (fun ω => ∑' i, ENNReal.ofReal (f i ω)) :=
    Measurable.tsum fun i => (hf i).ennreal_ofReal
  have hfinite : (∫⁻ ω, ∑' i, ENNReal.ofReal (f i ω) ∂μ) ≠ ⊤ :=
    (hbound.trans_lt ENNReal.ofReal_lt_top).ne
  have hsummable : ∀ᵐ ω ∂μ, Summable (fun i => f i ω) := by
    filter_upwards [ae_lt_top hsum_meas hfinite] with ω hω
    have h := ENNReal.summable_toReal hω.ne
    simpa only [ENNReal.toReal_ofReal (hf_nonneg _ _)] using h
  have hpoint : ∀ ω, ENNReal.ofReal (∑' i, f i ω) ≤ ∑' i, ENNReal.ofReal (f i ω) := by
    intro ω
    by_cases h : Summable (fun i => f i ω)
    · exact (ENNReal.ofReal_tsum_of_nonneg (fun i => hf_nonneg i ω) h).le
    · simp [tsum_eq_zero_of_not_summable h]
  have hlin : (∫⁻ ω, ENNReal.ofReal (∑' i, f i ω) ∂μ) ≤ ENNReal.ofReal C :=
    (lintegral_mono hpoint).trans hbound
  have hmeas : Measurable (fun ω => ∑' i, f i ω) := Measurable.tsum hf
  have hnonneg : ∀ᵐ ω ∂μ, 0 ≤ ∑' i, f i ω :=
    Filter.Eventually.of_forall fun ω => tsum_nonneg (fun i => hf_nonneg i ω)
  have hint : Integrable (fun ω => ∑' i, f i ω) μ :=
    ⟨hmeas.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnonneg).2
      (hlin.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hsummable, hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas.aestronglyMeasurable]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans_eq (ENNReal.toReal_ofReal hC)

end Invariant233.MaskedTail

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OmittedEvents
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace InvariantProjection.ConditionalConvolution

open MeasureTheory

theorem selector_outside (K n : ℕ) (v : ℤ) (hv : v ∉ window K n) :
    (K : ℤ) < |selector K n v| := by
  unfold selector
  split_ifs with h
  · exact h
  · have hv' := mt (mem_window_iff K n v).mpr hv
    push Not at hv'
    exact hv' (le_of_not_gt h)

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

theorem measurableSet_omittedEvent (H : ℤ → Set Ω) (K n : ℕ)
    (hH : ∀ k : ℤ, (K : ℤ) < |k| → MeasurableSet (H k)) (v : ℤ) :
    MeasurableSet (omittedEvent H K n v) := by
  unfold omittedEvent
  split_ifs with hv
  · exact MeasurableSet.empty
  · exact hH _ (selector_outside K n v hv)

theorem measurableSet_omittedMask (H : ℤ → Set Ω) (K n : ℕ)
    (hH : ∀ k : ℤ, (K : ℤ) < |k| → MeasurableSet (H k)) :
    MeasurableSet {z : Ω × ℤ | z.1 ∈ omittedEvent H K n z.2} := by
  have he : {z : Ω × ℤ | z.1 ∈ omittedEvent H K n z.2} =
      ⋃ v : ℤ, (omittedEvent H K n v) ×ˢ ({v} : Set ℤ) := by
    ext z
    simp
  rw [he]
  exact MeasurableSet.iUnion (fun v =>
    (measurableSet_omittedEvent H K n hH v).prod (measurableSet_singleton v))

theorem condExp_omittedEvent_le (μ : Measure Ω) (m : MeasurableSpace Ω)
    (H : ℤ → Set Ω) (K n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hH : ∀ k : ℤ, (K : ℤ) < |k| →
      μ[(H k).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ) :
    ∀ v : ℤ, μ[(omittedEvent H K n v).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ := by
  intro v
  by_cases hv : v ∈ window K n
  · simp only [omittedEvent, ite_eq_left hv, Set.indicator_empty]
    change μ[(0 : Ω → ℝ) | m] ≤ᵐ[μ] fun _ => δ
    rw [condExp_zero]
    exact Filter.Eventually.of_forall (fun _ => hδ)
  · simpa only [omittedEvent, ite_eq_right hv] using hH _ (selector_outside K n v hv)

theorem condExp_omittedMask_section_le (μ : Measure Ω) (m : MeasurableSpace Ω)
    (H : ℤ → Set Ω) (K n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hH : ∀ k : ℤ, (K : ℤ) < |k| →
      μ[(H k).indicator (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ) :
    ∀ v : ℤ,
      μ[({ω | (ω, v) ∈ {z : Ω × ℤ | z.1 ∈ omittedEvent H K n z.2}}).indicator
        (fun _ => (1 : ℝ)) | m] ≤ᵐ[μ] fun _ => δ := by
  let : MeasurableSpace Ω := mΩ
  exact condExp_omittedEvent_le (mΩ := mΩ) μ m H K n hδ hH

end InvariantProjection.ConditionalConvolution

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_OrbitInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.OrbitInvariance

section Ring
variable {A : Type*} [Ring A] {p T : A}

theorem invariant_iff_compression :
    (1 - p) * T * p = 0 ↔ p * T * p = T * p := by
  rw [sub_mul, one_mul, sub_mul]
  exact sub_eq_zero.trans eq_comm

theorem invariant_pow (hp : IsIdempotentElem p)
    (hT : (1 - p) * T * p = 0) (n : ℕ) :
    (1 - p) * T ^ n * p = 0 := by
  have hTp : p * T * p = T * p := invariant_iff_compression.mp hT
  apply invariant_iff_compression.mpr
  induction n with
  | zero => simpa using hp.eq
  | succ n ih =>
    calc
      p * T ^ (n + 1) * p = p * T ^ n * (T * p) := by rw [pow_succ]; simp [mul_assoc]
      _ = p * T ^ n * (p * T * p) := by rw [hTp]
      _ = (p * T ^ n * p) * T * p := by simp [mul_assoc]
      _ = (T ^ n * p) * T * p := by rw [ih]
      _ = T ^ n * (p * T * p) := by simp [mul_assoc]
      _ = T ^ n * (T * p) := by rw [hTp]
      _ = T ^ (n + 1) * p := by rw [pow_succ]; simp [mul_assoc]

theorem endpoint_inclusion_pow {q D : A} (hq : IsIdempotentElem q)
    (hT : (1 - q) * T * q = 0) (hD : (1 - q) * D * p = 0) (n : ℕ) :
    (1 - q) * T ^ n * D * p = 0 := by
  have hD' : q * (D * p) = D * p := by
    rw [sub_mul, one_mul, sub_mul, sub_eq_zero] at hD
    simpa only [mul_assoc] using hD.symm
  calc
    (1 - q) * T ^ n * D * p = ((1 - q) * T ^ n) * (D * p) := by
      simp only [mul_assoc]
    _ = ((1 - q) * T ^ n) * (q * (D * p)) := by rw [hD']
    _ = ((1 - q) * T ^ n * q) * (D * p) := by simp only [mul_assoc]
    _ = 0 := by rw [invariant_pow hq hT n, zero_mul]

end Ring


end Invariant233.OrbitInvariance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RepresentedFieldInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
namespace Invariant233.DirectIntegral

variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [Countable ι]

theorem ae_invariant_of_representations (b : HilbertBasis ι ℂ E)
    (P T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F G : X → E →L[ℂ] E)
    (hP : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun x => F x (ξ x))
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun x => G x (ξ x))
    (hinv : (1 - P) * T * P = 0) :
    ∀ᵐ x ∂μ, (1 - F x) * G x * F x = 0 := by
  apply Fields.ae_eq_of_countable_columns
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  intro i
  let ξ : Lp E 2 μ := Lp.const 2 μ (b i)
  have heq : T (P ξ) = P (T (P ξ)) := by
    have h := congrArg (fun A : Lp E 2 μ →L[ℂ] Lp E 2 μ => A ξ) hinv
    change T (P ξ) - P (T (P ξ)) = 0 at h
    exact sub_eq_zero.mp h
  filter_upwards [hP ξ, hT (P ξ), hP (T (P ξ)), Lp.coeFn_const 2 μ (b i)]
    with x hPx hTx hPTx hξ
  have hx := congrArg (fun η : Lp E 2 μ => η x) heq
  change ξ x = b i at hξ
  rw [hTx, hPTx, hTx, hPx, hξ] at hx
  change G x (F x (b i)) - F x (G x (F x (b i))) = 0
  exact sub_eq_zero.mpr hx

end Invariant233.DirectIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FiniteSupportWeights
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.FiniteSupportWeights

variable {X ι κ : Type*} [MeasurableSpace X]

theorem ae_mem_integerCore (μ : Measure X) (σ : ℤ → X → X) (s : Set X)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ) (hs : ∀ᵐ x ∂μ, x ∈ s) :
    ∀ᵐ x ∂μ, x ∈ integerCore σ s := by
  exact ae_all_iff.mpr fun n => (hσ n).quasiMeasurePreserving.ae hs

theorem measurableSet_integerCore (σ : ℤ → X → X) (s : Set X)
    (hσ : ∀ n, Measurable (σ n)) (hs : MeasurableSet s) :
    MeasurableSet (integerCore σ s) := by
  have heq : integerCore σ s = ⋂ n : ℤ, σ n ⁻¹' s := by
    ext x
    simp [integerCore]
  rw [heq]
  exact MeasurableSet.iInter fun n => hs.preimage (hσ n)

omit [MeasurableSpace X] in

theorem integerCore_subset (σ : ℤ → X → X) (s : Set X)
    (hzero : ∀ x, σ 0 x = x) : integerCore σ s ⊆ s := by
  intro x hx
  simpa only [hzero] using hx 0

omit [MeasurableSpace X] in

theorem mem_integerCore_translate_iff (σ : ℤ → X → X) (s : Set X)
    (hadd : ∀ m n x, σ (m + n) x = σ m (σ n x)) (n : ℤ) (x : X) :
    σ n x ∈ integerCore σ s ↔ x ∈ integerCore σ s := by
  constructor
  · intro hx m
    have hm := hx (m - n)
    simpa only [← hadd, sub_add_cancel] using hm
  · intro hx m
    simpa only [← hadd] using hx (m + n)

theorem uniform_nonzero_floor_of_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal t := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico (1 - t) 1 := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨?_, hu1⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, ?_, hu1⟩
      · intro h
        linarith [h.2]
      · linarith
  rw [hset, Real.volume_Ico]
  congr 1
  ring

theorem uniform_nonzero_floor_of_nonpos {t : ℝ} (ht0 : -1 ≤ t) (ht1 : t ≤ 0) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} =
      ENNReal.ofReal (-t) := by
  have hmeas : MeasurableSet {u : ℝ | Int.floor (u + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  rw [Measure.restrict_apply hmeas]
  have hset : {u : ℝ | Int.floor (u + t) ≠ 0} ∩ Set.Ico 0 1 =
      Set.Ico 0 (-t) := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, ne_eq, Int.floor_eq_zero_iff,
      Set.mem_Ico]
    constructor
    · rintro ⟨hn, hu0, hu1⟩
      refine ⟨hu0, ?_⟩
      by_contra h
      apply hn
      constructor <;> linarith
    · rintro ⟨hu0, hu1⟩
      refine ⟨?_, hu0, ?_⟩
      · intro h
        linarith [h.1]
      · linarith
  rw [hset, Real.volume_Ico, sub_zero]

theorem uniform_nonzero_floor_le (t : ℝ) :
    (volume.restrict (Set.Ico (0 : ℝ) 1)) {u | Int.floor (u + t) ≠ 0} ≤
      ENNReal.ofReal |t| := by
  by_cases ht : |t| ≤ 1
  · have ht' := abs_le.mp ht
    rcases le_total 0 t with hpos | hneg
    · rw [uniform_nonzero_floor_of_nonneg hpos ht'.2, abs_of_nonneg hpos]
    · rw [uniform_nonzero_floor_of_nonpos ht'.1 hneg, abs_of_nonpos hneg]
  · calc
      _ ≤ (volume.restrict (Set.Ico (0 : ℝ) 1)) Set.univ := measure_mono (Set.subset_univ _)
      _ = ENNReal.ofReal 1 := by simp
      _ ≤ ENNReal.ofReal |t| := ENNReal.ofReal_le_ofReal (le_of_lt (lt_of_not_ge ht))

theorem measure_nonzero_floor_le (μ : Measure X) (u : X → ℝ)
    (hu : MeasurePreserving u μ (volume.restrict (Set.Ico (0 : ℝ) 1))) (t : ℝ) :
    μ {x | Int.floor (u x + t) ≠ 0} ≤ ENNReal.ofReal |t| := by
  have hmeas : MeasurableSet {v : ℝ | Int.floor (v + t) ≠ 0} :=
    (measurableSet_eq_fun (measurable_id.add_const t).floor measurable_const).compl
  change μ (u ⁻¹' {v : ℝ | Int.floor (v + t) ≠ 0}) ≤ _
  rw [hu.measure_preimage hmeas.nullMeasurableSet]
  exact uniform_nonzero_floor_le t

theorem measurableSet_finite_support {R : Type*} [MeasurableSpace R]
    [MeasurableSingletonClass R] [Zero R] [Countable ι]
    (a : ι → X → R) (ha : ∀ i, Measurable (a i)) :
    MeasurableSet {x | (Function.support (fun i => a i x)).Finite} := by
  classical
  have heq : {x | (Function.support (fun i => a i x)).Finite} =
      ⋃ s : Finset ι, ⋂ i : ι, ⋂ (_ : i ∉ s), {x | a i x = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
    constructor
    · intro hx
      refine ⟨hx.toFinset, ?_⟩
      intro i hi
      by_contra hne
      exact hi (hx.mem_toFinset.mpr hne)
    · rintro ⟨s, hs⟩
      apply s.finite_toSet.subset
      intro i hi
      by_contra his
      exact hi (hs i his)
  rw [heq]
  refine MeasurableSet.iUnion fun s => MeasurableSet.iInter fun i =>
    MeasurableSet.iInter fun _ => ?_
  exact (ha i) (measurableSet_singleton 0)

theorem ae_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) (k : ℤ) :
    ∀ᵐ x ∂μ, (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  have hs : Summable (fun i => |(k : ℝ)| * α i) := hα.mul_left _
  have hbound : (∑' i, μ {x | Int.floor (u i x + (k : ℝ) * α i) ≠ 0}) ≤
      ∑' i, ENNReal.ofReal (|(k : ℝ)| * α i) := by
    apply ENNReal.tsum_le_tsum
    intro i
    simpa only [abs_mul, abs_of_nonneg (hα0 i)] using
      measure_nonzero_floor_le μ (u i) (hu i) ((k : ℝ) * α i)
  exact ae_finite_setOfPred_mem (lt_of_le_of_lt hbound hs.tsum_ofReal_lt_top).ne

theorem ae_all_finite_floor_support [Countable ι] (μ : Measure X) (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∀ᵐ x ∂μ, ∀ k : ℤ,
      (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  exact ae_all_iff.mpr fun k => ae_finite_floor_support μ u hu α hα0 hα k

theorem exists_invariant_conull_floor_support [Countable ι]
    (μ : Measure X) (σ : ℤ → X → X)
    (hσ : ∀ n, MeasurePreserving (σ n) μ μ)
    (hzero : ∀ x, σ 0 x = x)
    (hadd : ∀ m n x, σ (m + n) x = σ m (σ n x))
    (u : ι → X → ℝ)
    (hu : ∀ i, MeasurePreserving (u i) μ (volume.restrict (Set.Ico (0 : ℝ) 1)))
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∃ s : Set X, MeasurableSet s ∧ (∀ᵐ x ∂μ, x ∈ s) ∧
      (∀ n x, σ n x ∈ s ↔ x ∈ s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        (Function.support (fun i => Int.floor (u i x + (k : ℝ) * α i))).Finite := by
  let a : ℤ → ι → X → ℤ := fun k i x => Int.floor (u i x + (k : ℝ) * α i)
  let s₀ : Set X := {x | ∀ k : ℤ, (Function.support (fun i => a k i x)).Finite}
  have hs₀ : MeasurableSet s₀ := by
    have heq : s₀ = ⋂ k : ℤ, {x | (Function.support (fun i => a k i x)).Finite} := by
      ext x
      simp [s₀]
    rw [heq]
    exact MeasurableSet.iInter fun k => measurableSet_finite_support (a k)
      (fun i => ((hu i).measurable.add_const _).floor)
  refine ⟨integerCore σ s₀,
    measurableSet_integerCore σ s₀ (fun n => (hσ n).measurable) hs₀, ?_, ?_, ?_⟩
  · exact ae_mem_integerCore μ σ s₀ hσ (ae_all_finite_floor_support μ u hu α hα0 hα)
  · exact mem_integerCore_translate_iff σ s₀ hadd
  · intro x hx
    exact integerCore_subset σ s₀ hzero hx

end Invariant233.FiniteSupportWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleWeightSupport
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.CircleWeightSupport

theorem exists_invariant_conull_floor_support {ι : Type*} [Countable ι]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∃ s : Set UnitAddCircle, MeasurableSet s ∧ (∀ᵐ x ∂volume, x ∈ s) ∧
      (∀ (n : ℤ) x, x + n • (θ : UnitAddCircle) ∈ s ↔ x ∈ s) ∧
      ∀ x ∈ s, ∀ k : ℤ,
        (Function.support (fun i =>
          Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) +
            (k : ℝ) * α i))).Finite := by
  apply FiniteSupportWeights.exists_invariant_conull_floor_support
    (volume : Measure UnitAddCircle) (fun n x => x + n • (θ : UnitAddCircle))
    (fun n => measurePreserving_add_right volume (n • (θ : UnitAddCircle)))
    (by intro x; simp)
    (by intro m n x; simp [add_zsmul, add_comm, add_left_comm])
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ))
    (fun i => measurePreserving_characterRepresentative (q i) (hq i)) α hα0 hα

end Invariant233.CircleWeightSupport

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_FloorCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleCharacterDynamics
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
namespace CircleCharacterDynamics

local notation "Circle" => AddCircle (1 : ℝ)
local notation "rep" => (fun x : Circle => (AddCircle.equivIco (1 : ℝ) 0 x : ℝ))

theorem coe_representative (x : Circle) : ((rep x : ℝ) : Circle) = x :=
  AddCircle.coe_equivIco

theorem representative_add_real (x : Circle) (t : ℝ) :
    rep (x + (t : Circle)) = Int.fract (rep x + t) := by
  rw [← representative_coe]
  congr 1
  rw [AddCircle.coe_add, coe_representative]

theorem zsmul_real_phase (q : ℤ) (θ : ℝ) :
    q • (θ : Circle) = ((Int.fract ((q : ℝ) * θ) : ℝ) : Circle) := by
  rw [AddCircle.coe_fract]
  simpa only [zsmul_eq_mul] using
    (AddCircle.coe_zsmul (p := (1 : ℝ)) (n := q) (x := θ)).symm

theorem character_orbit_representative (q v : ℤ) (θ : ℝ) (x : Circle) :
    rep (q • (x + v • (θ : Circle))) =
      Int.fract (rep (q • x) + (v : ℝ) * Int.fract ((q : ℝ) * θ)) := by
  rw [zsmul_add, smul_comm q v, zsmul_real_phase]
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  exact representative_add_real _ _

end CircleCharacterDynamics
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function

namespace Invariant233.CircleWeights

variable {ι : Type*}

theorem coordinate_mem_Ico (q : ι → ℤ) (i : ι) (x : UnitAddCircle) :
    coordinate q i x ∈ Ico (0 : ℝ) 1 := by
  simpa only [coordinate, representative, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 (q i • x)).property

theorem coordinate_rotate (θ : ℝ) (q : ι → ℤ) (i : ι)
    (k : ℤ) (x : UnitAddCircle) :
    coordinate q i (rotate θ k x) =
      Int.fract (coordinate q i x + (k : ℝ) * phase θ q i) := by
  exact CircleCharacterDynamics.character_orbit_representative (q i) k θ x

theorem cocycle_zero (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (x : UnitAddCircle) :
    cocycle θ q c 0 x = 1 := by
  simp only [cocycle, floorCost, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero
    (fun i => coordinate q i x) c (fun i => coordinate_mem_Ico q i x)

theorem exists_cocycle_set [Countable ι]
    (θ : ℝ) (q : ι → ℤ) (hq : ∀ i, q i ≠ 0) (c : ι → ℝ)
    (hphase : Summable (phase θ q)) :
    ∃ s : Set UnitAddCircle, MeasurableSet s ∧ (∀ᵐ x ∂volume, x ∈ s) ∧
      (∀ (k : ℤ) x, rotate θ k x ∈ s ↔ x ∈ s) ∧
      (∀ x ∈ s, ∀ k : ℤ,
        HasFiniteSupport (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i))) ∧
      (∀ x ∈ s, ∀ k n : ℤ,
        cocycle θ q c (k + n) x =
          cocycle θ q c n (rotate θ k x) * cocycle θ q c k x) := by
  obtain ⟨s, hs, hfull, hinv, hfinite⟩ :=
    CircleWeightSupport.exists_invariant_conull_floor_support θ q hq
      (phase θ q) (phase_nonneg θ q) hphase
  refine ⟨s, hs, hfull, hinv, hfinite, ?_⟩
  intro x hx k n
  have hk : HasFiniteSupport
      (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)) := hfinite x hx k
  have hn : HasFiniteSupport (fun i =>
      Int.floor (Int.fract (coordinate q i x + (k : ℝ) * phase θ q i) +
        (n : ℝ) * phase θ q i)) := by
    have h := hfinite (rotate θ k x) ((hinv k x).mpr hx) n
    change HasFiniteSupport (fun i =>
      Int.floor (coordinate q i (rotate θ k x) + (n : ℝ) * phase θ q i)) at h
    simpa only [coordinate_rotate] using h
  simpa only [cocycle, floorCost, coordinate_rotate] using
    FiniteSupportCocycle.exp_tsum_floor_cocycle
      (fun i => coordinate q i x) (phase θ q) c k n hk hn

theorem cocycle_antitone_of_finite_support (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i) (x : UnitAddCircle)
    (hx : ∀ k : ℤ, HasFiniteSupport
      (fun i => Int.floor (coordinate q i x + (k : ℝ) * phase θ q i))) :
    Antitone (fun k : ℤ => cocycle θ q c k x) := by
  intro k n hkn
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply Summable.tsum_le_tsum _
    (FiniteSupportCocycle.summable_weighted_int c (hx k))
    (FiniteSupportCocycle.summable_weighted_int c (hx n))
  intro i
  apply mul_le_mul_of_nonneg_left _ (hc i)
  apply Int.cast_le.mpr
  apply Int.floor_mono
  exact add_le_add (le_refl _)
    (mul_le_mul_of_nonneg_right (Int.cast_le.mpr hkn) (phase_nonneg θ q i))

end Invariant233.CircleWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterBlocks
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.CircleParameterData

theorem block_index_unique (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {j k i : ℕ}
    (hij : i ∈ p.block j) (hik : i ∈ p.block k) : j = k := by
  have hj := (p.mem_block_iff j i).mp hij
  have hk := (p.mem_block_iff k i).mp hik
  have hmono := (p.blockEnd_strictMono hm).monotone
  apply le_antisymm
  · by_contra h
    have hjk : k ≤ j - 1 := by omega
    have hd := hmono hjk
    omega
  · by_contra h
    have hjk : j ≤ k - 1 := by omega
    have hd := hmono hjk
    omega

theorem flattenedCost_eq_of_mem (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) {j n : ℕ} (hn : n + 1 ∈ p.block j) :
    p.flattenedCost n = p.C j := by
  simp only [flattenedCost, p.blockIndex_eq_of_mem hm hn]

end Invariant233.CircleParameterData

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open Filter
open scoped Topology

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem shifted_K_pos (n : ℕ) : 0 < (p.K (n + 1) : ℝ) := by
  exact_mod_cast hp.K_pos (n + 1) (by omega)

theorem shifted_K_double (n : ℕ) :
    2 * (p.K (n + 1) : ℝ) ≤ (p.K (n + 1 + 1) : ℝ) := by
  exact_mod_cast (hp.K_double (n + 1) (by omega)).le

theorem summable_reciprocal : Summable (fun n : ℕ => 1 / (p.K (n + 1) : ℝ)) :=
  ParameterTails.summable_reciprocal hp.shifted_K_pos hp.shifted_K_double

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CirclePhaseSummability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233
open scoped BigOperators ENNReal

namespace CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem block_phase_sum_le (j : ℕ) (hj : 1 ≤ j) :
    (∑ i ∈ p.block j, p.alpha θ i) ≤ 2 / (p.K j : ℝ) := by
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  calc
    (∑ i ∈ p.block j, p.alpha θ i) ≤ ∑ i ∈ p.block j, 2 / p.N j := by
      apply Finset.sum_le_sum
      intro i hi
      exact (hp.phase_bounds j hj i hi).2.le
    _ = ((p.block j).card : ℝ) * (2 / p.N j) := by simp
    _ = 2 / (p.K j : ℝ) := by
      rw [p.card_block j hj]
      simp only [CircleParameterData.N]
      field_simp

theorem summable_block_phases :
    Summable (fun n : ℕ => ∑ i ∈ p.block (n + 1), p.alpha θ i) := by
  apply Summable.of_nonneg_of_le
    (fun n => Finset.sum_nonneg (fun i _ => Int.fract_nonneg _))
    (fun n => hp.block_phase_sum_le (n + 1) (by omega))
  simpa only [mul_one_div] using hp.summable_reciprocal.mul_left 2

end CircleParameterLaws
end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ParameterCircleCocycle
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Function
open scoped BigOperators ENNReal

namespace Invariant233

namespace CircleParameterData

theorem coord_phase_eq (p : CircleParameterData) (θ : ℝ) (i : p.Coord) :
    CircleWeights.phase θ p.coordFrequency i = p.alpha θ i.2 := by
  simp only [CircleWeights.phase, coordFrequency, alpha, Int.cast_natCast]

theorem coord_coordinate_eq (p : CircleParameterData) (i : p.Coord) (x : Circle) :
    CircleWeights.coordinate p.coordFrequency i x = p.coordinate i.2 x := by
  simp only [CircleWeights.coordinate, CircleWeights.representative,
    coordFrequency, coordinate, rep, natCast_zsmul]

theorem floorCocycle_pos (p : CircleParameterData) (θ : ℝ) (k : ℤ) (x : Circle) :
    0 < p.floorCocycle θ k x := Real.exp_pos _

theorem floorCocycle_zero (p : CircleParameterData) (θ : ℝ) (x : Circle) :
    p.floorCocycle θ 0 x = 1 :=
  CircleWeights.cocycle_zero θ p.coordFrequency p.coordCost x

end CircleParameterData

namespace CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem summable_coord_phases : Summable (CircleWeights.phase θ p.coordFrequency) := by
  rw [show CircleWeights.phase θ p.coordFrequency =
    (fun i : p.Coord => p.alpha θ i.2) from funext (p.coord_phase_eq θ)]
  apply (summable_sigma_of_nonneg (fun i => Int.fract_nonneg _)).mpr
  constructor
  · intro j
    exact (hasSum_fintype _).summable
  · apply hp.summable_block_phases.congr
    intro j
    simp only [tsum_fintype]
    exact (Finset.sum_attach (p.block (j + 1)) (p.alpha θ)).symm

theorem measurable_parameter_cocycle (k : ℤ) : Measurable (p.floorCocycle θ k) :=
  CircleWeights.measurable_cocycle θ p.coordFrequency hp.coordFrequency_ne_zero
    p.coordCost k

theorem parameter_cocycle_antitone (x : Circle)
    (hx : ∀ k : ℤ, HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2))) :
    Antitone (fun k : ℤ => p.floorCocycle θ k x) := by
  apply CircleWeights.cocycle_antitone_of_finite_support θ p.coordFrequency p.coordCost
    (fun i => (hp.coordCost_pos i).le) x
  simpa only [p.coord_phase_eq, p.coord_coordinate_eq] using hx

theorem exists_parameter_cocycle_set :
    ∃ s : Set Circle, MeasurableSet s ∧ (∀ᵐ x ∂circleMeasure, x ∈ s) ∧
      (∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s) ∧
      (∀ x ∈ s, ∀ k : ℤ,
        HasFiniteSupport (fun i : p.Coord =>
          Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2))) ∧
      (∀ x ∈ s, ∀ k n : ℤ,
        p.floorCocycle θ (k + n) x =
          p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x) := by
  simpa only [circleMeasure, CircleParameterData.floorCocycle,
    p.coord_phase_eq, p.coord_coordinate_eq] using
    CircleWeights.exists_cocycle_set θ p.coordFrequency hp.coordFrequency_ne_zero
      p.coordCost hp.summable_coord_phases

end CircleParameterLaws
end Invariant233

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

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_DiagonalContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ENNReal lp

namespace Invariant233.SequenceHilbert

variable {I X : Type*}

theorem diagonal_congr (a b : I → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i, ‖a i‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ D)
    (hab : ∀ i, a i = b i) : diagonal a C hC ha = diagonal b D hD hb := by
  ext v i
  simp only [diagonal_apply, hab]

end Invariant233.SequenceHilbert

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_UnrestrictedDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SequenceHilbert

variable {I : Type*}

theorem boundedDiagonal_eq (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : boundedDiagonal a = diagonal a C hC ha := by
  unfold boundedDiagonal
  split
  · rename_i h
    exact diagonal_congr a a h.choose C h.choose_spec.1 hC h.choose_spec.2 ha (fun _ => rfl)
  · rename_i h
    exact False.elim (h ⟨C, hC, ha⟩)

@[simp]
theorem boundedDiagonal_apply_of_bound (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) (v : SequenceHilbert I) (i : I) :
    boundedDiagonal a v i = a i * v i := by
  rw [boundedDiagonal_eq a C hC ha, diagonal_apply]

end Invariant233.SequenceHilbert

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedOrbitInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.OrbitInvariance
open WeightedShift

theorem endpoint_orthogonality (D : Hilbert →L[ℂ] Hilbert)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsSelfAdjoint q)
    (h : (1 - q) * D * p = 0) (ξ η : Hilbert) :
    inner ℂ (D (p ξ)) ((1 - q) η) = 0 := by
  have hq' : ((1 - q : Hilbert →L[ℂ] Hilbert) : Hilbert →ₗ[ℂ] Hilbert).IsSymmetric :=
    LinearMap.IsSymmetric.id.sub hq.isSymmetric
  have hv : (1 - q) (D (p ξ)) = 0 :=
    congrArg (fun A : Hilbert →L[ℂ] Hilbert => A ξ) h
  calc
    inner ℂ (D (p ξ)) ((1 - q) η) =
        inner ℂ ((1 - q) (D (p ξ))) η :=
      (hq' _ _).symm
    _ = 0 := by rw [hv, inner_zero_left]

theorem weighted_shift_convolution_hasSum (w r : Weight)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert) :
    HasSum (fun v : ℤ =>
      (orbitProduct w n v * r v * p ξ v) * star ((1 - q) η (v + n))) 0 := by
  have hpow : (1 - q) * ((operator w)^n * diagonal r) * p = 0 := by
    simpa only [mul_assoc] using endpoint_inclusion_pow hq.isIdempotentElem hT hpair n
  have horth : inner ℂ ((1 - q) η) (((operator w)^n) (diagonal r (p ξ))) = 0 :=
    inner_eq_zero_symm.mp (endpoint_orthogonality ((operator w)^n * diagonal r)
      hq.isSelfAdjoint hpow ξ η)
  have hs := lp.hasSum_inner (𝕜 := ℂ) ((1 - q) η)
    (((operator w)^n) (diagonal r (p ξ)))
  rw [horth] at hs
  have hs' := (Equiv.addRight (n : ℤ)).hasSum_iff.mpr hs
  change HasSum (fun v : ℤ => inner ℂ (((1 - q) η) (v + n))
    ((((operator w)^n) (diagonal r (p ξ))) (v + n))) 0 at hs'
  simpa only [RCLike.inner_apply,
    starRingEnd_apply, operator_pow_apply_add, diagonal_apply,
    orbitProduct_apply, mul_assoc] using hs'

theorem cocycle_coefficients_hasSum (w r : Weight) (Fx Fy : ℤ → ℝ)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert)
    (hratio : ∀ v : ℤ, orbitProduct w n v * r v =
      (Fy (v + n) : ℂ) / (Fx v : ℂ)) :
    let A : ℤ → ℂ := fun v => p ξ v / (Fx v : ℂ)
    let B : ℤ → ℂ := fun v => (Fy (-v) : ℂ) * star ((1 - q) η (-v))
    HasSum (fun v : ℤ => A v * B (-(n : ℤ) - v)) 0 := by
  dsimp only
  apply (weighted_shift_convolution_hasSum w r hq hT hpair n ξ η).congr_fun
  intro v
  have hindex : -(-(n : ℤ) - v) = v + n := by omega
  rw [hindex, hratio v]
  simp only [div_eq_mul_inv]
  ring

theorem cocycle_coefficients_absolute_and_zero (w r : Weight) (Fx Fy : ℤ → ℝ)
    {p q : Hilbert →L[ℂ] Hilbert} (hq : IsStarProjection q)
    (hT : (1 - q) * operator w * q = 0)
    (hpair : (1 - q) * diagonal r * p = 0)
    (n : ℕ) (ξ η : Hilbert)
    (hratio : ∀ v : ℤ, orbitProduct w n v * r v =
      (Fy (v + n) : ℂ) / (Fx v : ℂ)) :
    let A : ℤ → ℂ := fun v => p ξ v / (Fx v : ℂ)
    let B : ℤ → ℂ := fun v => (Fy (-v) : ℂ) * star ((1 - q) η (-v))
    (Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖)) ∧
      (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  have hs := cocycle_coefficients_hasSum w r Fx Fy hq hT hpair n ξ η hratio
  exact ⟨hs.summable.norm, hs.tsum_eq⟩

end Invariant233.OrbitInvariance

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterOrbitIdentity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Invariant233
namespace CircleParameterData

theorem weight_product_eq_floorCocycle (p : CircleParameterData) (θ : ℝ)
    (x : Circle)
    (hc : ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    (n : ℕ) :
    (∏ j ∈ Finset.range n, (p.measurableWeight θ (Rotation.action θ (j : ℤ) x) : ℂ)) =
      (p.floorCocycle θ (n : ℤ) x : ℂ) := by
  induction n with
  | zero => simp [p.floorCocycle_zero]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have h := hc (n : ℤ) 1
    rw [Nat.cast_add, Nat.cast_one, h]
    change (p.floorCocycle θ n x : ℂ) *
      (p.floorCocycle θ 1 (CircleWeights.rotate θ n x) : ℂ) = _
    rw [Complex.ofReal_mul, mul_comm]

end CircleParameterData

namespace SequenceHilbert

theorem boundedDiagonal_eq_weighted (w : WeightedShift.Weight) :
    boundedDiagonal (fun k : ℤ => w k) = WeightedShift.diagonal w := by
  ext ξ k
  rw [boundedDiagonal_apply_of_bound (fun k : ℤ => w k) ‖w‖ (norm_nonneg _)
    (fun k => lp.norm_apply_le_norm (by simp) w k)]
  rfl

end SequenceHilbert

namespace CircleParameterLaws
open CircleParameterData Rotation WeightedShift
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem measurableOperator_ae (ξ : Rotation.Hilbert) :
    p.measurableOperator θ hp ξ =ᵐ[circleMeasure]
      fun x => WeightedShift.operator (hp.parameterOrbitWeight x) (ξ x) := by
  filter_upwards [Rotation.U_mul_measurableRepresentation_coordinates_ae θ
    (fun z => (p.measurableWeight θ z : ℂ)) 1 (by norm_num)
    (Complex.measurable_ofReal.comp (p.measurableWeight_borel θ))
    (p.measurableWeight_operator_bound θ hp) ξ] with x hx
  exact lp.ext (funext hx)

end CircleParameterLaws
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterConvolutionIdentity
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Invariant233.CircleParameterLaws
open CircleParameterData WeightedShift

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem parameter_orbitProduct_eq_floorCocycle {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    {y : Circle} (hy : y ∈ s) (n : ℕ) (v : ℤ) :
    orbitProduct (hp.parameterOrbitWeight y) n v =
      (p.floorCocycle θ (n : ℤ) (Rotation.action θ v y) : ℂ) := by
  rw [orbitProduct_apply]
  have hprod := p.weight_product_eq_floorCocycle θ (Rotation.action θ v y)
    (hc _ ((hinv v y).mpr hy)) n
  convert hprod using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.prod_congr rfl
  intro j hj
  change (p.measurableWeight θ (Rotation.action θ (v + j) y) : ℂ) =
    (p.measurableWeight θ (Rotation.action θ (j : ℤ) (Rotation.action θ v y)) : ℂ)
  rw [Rotation.action_add, add_comm v]

theorem parameter_orbitProduct_mul_ratio {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    (x : Circle) {y : Circle} (hy : y ∈ s) (n : ℕ) (v : ℤ) :
    orbitProduct (hp.parameterOrbitWeight y) n v *
        ((p.floorCocycle θ v y / p.floorCocycle θ v x : ℝ) : ℂ) =
      (p.floorCocycle θ (v + n) y : ℂ) / (p.floorCocycle θ v x : ℂ) := by
  rw [hp.parameter_orbitProduct_eq_floorCocycle hinv hc hy n v,
    hc y hy v n, Complex.ofReal_mul, Complex.ofReal_div]
  simp only [Rotation.action, CircleWeights.rotate]
  ring

theorem parameter_convolution_absolute_and_zero {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    (x : Circle) {y : Circle} (hy : y ∈ s)
    (P Q : Hilbert →L[ℂ] Hilbert) (hQ : IsStarProjection Q)
    (hT : (1 - Q) * operator (hp.parameterOrbitWeight y) * Q = 0)
    (hpair : (1 - Q) * ratioDiagonal (p.floorCocycle θ) (x, y) * P = 0)
    (hbound : ∀ v : ℤ, p.floorCocycle θ v y / p.floorCocycle θ v x ≤ 1)
    (n : ℕ) (ξ η : Hilbert) :
    let A : ℤ → ℂ := fun v => P ξ v / (p.floorCocycle θ v x : ℂ)
    let B : ℤ → ℂ := fun v => (p.floorCocycle θ (-v) y : ℂ) * star ((1 - Q) η (-v))
    Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖) ∧
      (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  let r : Weight := ⟨fun v => ((p.floorCocycle θ v y / p.floorCocycle θ v x : ℝ) : ℂ),
    memℓp_infty <| by
      refine ⟨1, ?_⟩
      rintro a ⟨v, rfl⟩
      change ‖((p.floorCocycle θ v y / p.floorCocycle θ v x : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos (p.floorCocycle_pos θ v y) (p.floorCocycle_pos θ v x))]
      exact hbound v⟩
  have hd : ratioDiagonal (p.floorCocycle θ) (x, y) = diagonal r :=
    SequenceHilbert.boundedDiagonal_eq_weighted r
  rw [hd] at hpair
  exact OrbitInvariance.cocycle_coefficients_absolute_and_zero
    (hp.parameterOrbitWeight y) r (fun v => p.floorCocycle θ v x)
    (fun v => p.floorCocycle θ v y) hQ hT hpair n ξ η
    (hp.parameter_orbitProduct_mul_ratio hinv hc x hy n)

theorem ae_parameter_convolution_absolute_and_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → Circle) (hy : AEMeasurable y μ)
    (hyac : Measure.map y μ ≪ circleMeasure)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hF : ∀ z, IsStarProjection (F z))
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun z => F z (ξ z))
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hpair : ∀ᵐ ω ∂μ,
      (1 - F (y ω)) * ratioDiagonal (p.floorCocycle θ) (x ω, y ω) * F (x ω) = 0)
    (hbound : ∀ᵐ ω ∂μ, ∀ v : ℤ,
      p.floorCocycle θ v (y ω) / p.floorCocycle θ v (x ω) ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (ξ η : Hilbert),
      let A : ℤ → ℂ := fun v => F (x ω) ξ v / (p.floorCocycle θ v (x ω) : ℂ)
      let B : ℤ → ℂ := fun v => (p.floorCocycle θ (-v) (y ω) : ℂ) *
        star ((1 - F (y ω)) η (-v))
      Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖) ∧
        (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  have hlocal := DirectIntegral.ae_invariant_of_representations
    (default : HilbertBasis ℤ ℂ Rotation.Fiber) P (p.measurableOperator θ hp) F
    (fun z => operator (hp.parameterOrbitWeight z)) hrep hp.measurableOperator_ae hT
  obtain ⟨s, _, hfull, hs, _, hc⟩ := hp.exists_parameter_cocycle_set
  have hylocal := ae_of_ae_map hy (hyac.ae_le hlocal)
  have hyfull := ae_of_ae_map hy (hyac.ae_le hfull)
  filter_upwards [hylocal, hyfull, hpair, hbound] with ω hloc hys hpa hbo
  intro n ξ η
  exact hp.parameter_convolution_absolute_and_zero hs hc (x ω) hys
    (F (x ω)) (F (y ω)) (hF (y ω)) hloc hpa hbo n ξ η

theorem parameter_convolution_ratio_bounds (x y : Circle)
    (hx : ∀ k : ℤ, Function.HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2)))
    (hy : ∀ k : ℤ, Function.HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 y + (k : ℝ) * p.alpha θ i.2)))
    (hbound : ∀ v : ℤ, p.floorCocycle θ v y / p.floorCocycle θ v x ≤ 1)
    (n : ℕ) (v : ℤ) :
    0 < p.floorCocycle θ ((n : ℤ) + v) y / p.floorCocycle θ v x ∧
      p.floorCocycle θ ((n : ℤ) + v) y / p.floorCocycle θ v x ≤
        min (p.floorCocycle θ v y / p.floorCocycle θ v x)
          (p.floorCocycle θ ((n : ℤ) + v) y / p.floorCocycle θ ((n : ℤ) + v) x) ∧
      min (p.floorCocycle θ v y / p.floorCocycle θ v x)
          (p.floorCocycle θ ((n : ℤ) + v) y / p.floorCocycle θ ((n : ℤ) + v) x) ≤ 1 := by
  have hle : v ≤ (n : ℤ) + v := by omega
  have hmx := hp.parameter_cocycle_antitone x hx hle
  have hmy := hp.parameter_cocycle_antitone y hy hle
  refine ⟨div_pos (p.floorCocycle_pos θ _ y) (p.floorCocycle_pos θ v x),
    le_min ?_ ?_, (min_le_left _ _).trans (hbound v)⟩
  · exact (div_le_div_iff_of_pos_right (p.floorCocycle_pos θ v x)).mpr hmy
  · exact div_le_div_of_nonneg_left (p.floorCocycle_pos θ _ y).le
      (p.floorCocycle_pos θ _ x) hmx

theorem ae_parameter_convolution_ratio_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → Circle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hxac : Measure.map x μ ≪ circleMeasure) (hyac : Measure.map y μ ≪ circleMeasure)
    (hbound : ∀ᵐ ω ∂μ, ∀ v : ℤ,
      p.floorCocycle θ v (y ω) / p.floorCocycle θ v (x ω) ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (v : ℤ),
      0 < p.floorCocycle θ ((n : ℤ) + v) (y ω) / p.floorCocycle θ v (x ω) ∧
      p.floorCocycle θ ((n : ℤ) + v) (y ω) / p.floorCocycle θ v (x ω) ≤
        min (p.floorCocycle θ v (y ω) / p.floorCocycle θ v (x ω))
          (p.floorCocycle θ ((n : ℤ) + v) (y ω) /
            p.floorCocycle θ ((n : ℤ) + v) (x ω)) ∧
      min (p.floorCocycle θ v (y ω) / p.floorCocycle θ v (x ω))
          (p.floorCocycle θ ((n : ℤ) + v) (y ω) /
            p.floorCocycle θ ((n : ℤ) + v) (x ω)) ≤ 1 := by
  obtain ⟨s, _, hfull, _, hfinite, _⟩ := hp.exists_parameter_cocycle_set
  have hxfull := ae_of_ae_map hx (hxac.ae_le hfull)
  have hyfull := ae_of_ae_map hy (hyac.ae_le hfull)
  filter_upwards [hxfull, hyfull, hbound] with ω hxs hys hb
  intro n v
  exact hp.parameter_convolution_ratio_bounds (x ω) (y ω)
    (hfinite _ hxs) (hfinite _ hys) hb n v

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_PointwiseConvolution
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ComplexConjugate ENNReal lp

namespace InvariantProjection

theorem l2_masked_convolution_tail
    (s : Finset ℤ) (ξ γ : ℓ²(ℤ, ℂ)) (e : ℤ ≃ ℤ)
    (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (r : ℤ → ℝ) (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (H₁ H₂ : Set ℤ)
    (hzero : (∑' v : ℤ, (r v : ℂ) * ξ v * conj (γ (e v))) = 0)
    (hmask : ∀ v, v ∉ s → r v ≤ η + H₁.indicator (fun _ => (1 : ℝ)) v +
      H₂.indicator (fun _ => (1 : ℝ)) v) :
    ‖∑ v ∈ s, (r v : ℂ) * ξ v * conj (γ (e v))‖ ≤ η +
      (∑' v : ↑((s : Set ℤ)ᶜ), H₁.indicator (fun v => ‖ξ v‖ * ‖γ (e v)‖) v) +
      (∑' v : ↑((s : Set ℤ)ᶜ), H₂.indicator (fun v => ‖ξ v‖ * ‖γ (e v)‖) v) := by
  have hbase := l2_reindexed_absolute_products ξ γ e
  have hsum : (∑' v, ‖ξ v‖ * ‖γ (e v)‖) ≤ 1 := by
    refine hbase.2.trans ?_
    calc
      ‖ξ‖ * ‖γ‖ ≤ 1 * 1 := mul_le_mul hξ hγ (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hdom := norm_finset_sum_le_masked_tail s
    (fun v => (r v : ℂ) * ξ v * conj (γ (e v)))
    (fun v => ‖ξ v‖ * ‖γ (e v)‖) η H₁ H₂
    (l2_reindexed_multiplier_bound ξ γ e r hr).1 hzero hbase.1
    (fun v => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hη
    (fun v hv => by
      simp only [norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hr v).1]
      calc
        r v * ‖ξ v‖ * ‖γ (e v)‖ = r v * (‖ξ v‖ * ‖γ (e v)‖) := by ring
        _ ≤ (η + H₁.indicator (fun _ => (1 : ℝ)) v +
            H₂.indicator (fun _ => (1 : ℝ)) v) * (‖ξ v‖ * ‖γ (e v)‖) := by
          gcongr
          exact hmask v hv)
  refine hdom.trans ?_
  gcongr
  simpa using mul_le_mul_of_nonneg_left hsum hη

theorem l2_masked_convolution_tail_selector
    (s : Finset ℤ) (ξ γ : ℓ²(ℤ, ℂ)) (e : ℤ ≃ ℤ)
    (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (r : ℤ → ℝ) (hr : ∀ v, 0 ≤ r v ∧ r v ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (H₁ H₂ : Set ℤ) (k : ℤ → ℤ)
    (hzero : (∑' v : ℤ, (r v : ℂ) * ξ v * conj (γ (e v))) = 0)
    (hmask : ∀ v, v ∉ s → r v ≤ η + H₁.indicator (fun _ => (1 : ℝ)) (k v) +
      H₂.indicator (fun _ => (1 : ℝ)) (k v)) :
    ‖∑ v ∈ s, (r v : ℂ) * ξ v * conj (γ (e v))‖ ≤ η +
      (∑' v : ↑((s : Set ℤ)ᶜ),
        (H₁.indicator (fun _ => (1 : ℝ)) (k v)) * (‖ξ v‖ * ‖γ (e v)‖)) +
      (∑' v : ↑((s : Set ℤ)ᶜ),
        (H₂.indicator (fun _ => (1 : ℝ)) (k v)) * (‖ξ v‖ * ‖γ (e v)‖)) := by
  classical
  have hind (H : Set ℤ) (v : ℤ) :
      (k ⁻¹' H).indicator (fun v => ‖ξ v‖ * ‖γ (e v)‖) v =
        H.indicator (fun _ => (1 : ℝ)) (k v) * (‖ξ v‖ * ‖γ (e v)‖) := by
    by_cases hv : k v ∈ H <;> simp [hv]
  have hone (H : Set ℤ) (v : ℤ) :
      (k ⁻¹' H).indicator (fun _ => (1 : ℝ)) v =
        H.indicator (fun _ => (1 : ℝ)) (k v) := by
    simp only [Set.indicator_apply, Set.mem_preimage]
  have h := l2_masked_convolution_tail s ξ γ e hξ hγ r hr η hη
    (k ⁻¹' H₁) (k ⁻¹' H₂) hzero (by simpa only [hone] using hmask)
  simpa only [hind] using h

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformQuantization
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Invariant233.UniformQuantization

theorem quantize_eq_iff {q : ℕ} [NeZero q] (a : Fin q) {x : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) :
    quantize q x = a ↔ x ∈ Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hnonneg : 0 ≤ (q : ℝ) * x := mul_nonneg hq.le hx.1
  have hfloor : ⌊(q : ℝ) * x⌋₊ < q := (Nat.floor_lt hnonneg).mpr (by nlinarith [hx.2])
  change (⟨⌊(q : ℝ) * x⌋₊ % q, _⟩ : Fin q) = a ↔ _
  rw [Fin.ext_iff]
  change (⌊(q : ℝ) * x⌋₊ % q = a.val) ↔ _
  rw [Nat.mod_eq_of_lt hfloor, Nat.floor_eq_iff hnonneg]
  simp only [mem_Ico]
  constructor
  · intro h
    exact ⟨(div_le_iff₀ hq).mpr (by nlinarith [h.1]),
      (lt_div_iff₀ hq).mpr (by nlinarith [h.2])⟩
  · intro h
    constructor
    · have := (div_le_iff₀ hq).mp h.1
      nlinarith
    · have := (lt_div_iff₀ hq).mp h.2
      nlinarith

theorem preimage_singleton_inter_unit {q : ℕ} [NeZero q] (a : Fin q) :
    (quantize q ⁻¹' {a}) ∩ Ico (0 : ℝ) 1 =
      Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  ext x
  constructor
  · rintro ⟨hxa, hx⟩
    exact (quantize_eq_iff a hx).mp hxa
  · intro hx
    have hunit : x ∈ Ico (0 : ℝ) 1 := by
      constructor
      · exact (div_nonneg (by positivity) hq.le).trans hx.1
      · have ha : (a : ℝ) + 1 ≤ q := by exact_mod_cast Nat.succ_le_of_lt a.isLt
        have hbound : ((a : ℝ) + 1) / q ≤ 1 := (div_le_iff₀ hq).mpr (by linarith)
        exact hx.2.trans_le hbound
    exact ⟨(quantize_eq_iff a hunit).mpr hx, hunit⟩

theorem map_quantize_singleton (q : ℕ) [NeZero q] (a : Fin q) :
    (volume.restrict (Ico (0 : ℝ) 1)).map (quantize q) {a} = (q : ℝ≥0∞)⁻¹ := by
  rw [Measure.map_apply (measurable_quantize q) (measurableSet_singleton a),
    Measure.restrict_apply ((measurable_quantize q) (measurableSet_singleton a)),
    preimage_singleton_inter_unit, Real.volume_Ico]
  have hq : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have heq : ((a : ℝ) + 1) / q - (a : ℝ) / q = 1 / q := by ring
  rw [heq, ENNReal.ofReal_div_of_pos hq]
  simp

end Invariant233.UniformQuantization

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalConvolutionPointwise
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.InvariantProjection.ConditionalConvolution.mem_window_iff
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ComplexConjugate ENNReal lp

namespace InvariantProjection.ConditionalConvolution

theorem tsum_omittedEvent {Ω : Type*} (H : ℤ → Set Ω) (K n : ℕ)
    (ω : Ω) (w : ℤ → ℝ) :
    (∑' v : ↑(((window K n) : Set ℤ)ᶜ),
      (H (selector K n v)).indicator (fun _ => (1 : ℝ)) ω * w v) =
    ∑' v : ℤ, (omittedEvent H K n v).indicator (fun _ => (1 : ℝ)) ω * w v := by
  classical
  rw [tsum_subtype (((window K n) : Set ℤ)ᶜ)
    (fun v : ℤ => (H (selector K n v)).indicator (fun _ => (1 : ℝ)) ω * w v)]
  apply tsum_congr
  intro v
  by_cases hv : v ∈ window K n <;> simp [omittedEvent, hv]

theorem pointwise_bound {Ω : Type*} (K n : ℕ) (Fx Fy : ℤ → ℝ)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (H₁ H₂ : ℤ → Set Ω) (ω : Ω)
    (hratio : ∀ v : ℤ, 0 < Fy ((n : ℤ) + v) / Fx v ∧
      Fy ((n : ℤ) + v) / Fx v ≤ min (Fy v / Fx v)
        (Fy ((n : ℤ) + v) / Fx ((n : ℤ) + v)) ∧
      min (Fy v / Fx v) (Fy ((n : ℤ) + v) / Fx ((n : ℤ) + v)) ≤ 1)
    (hzero : (∑' v : ℤ, (ξ v / (Fx v : ℂ)) *
      ((Fy ((n : ℤ) + v) : ℂ) * conj (γ ((n : ℤ) + v)))) = 0)
    (htail : ∀ k : ℤ, (K : ℤ) < |k| → Fy k / Fx k ≤ η +
      (H₁ k).indicator (fun _ => (1 : ℝ)) ω +
      (H₂ k).indicator (fun _ => (1 : ℝ)) ω) :
    ‖truncated K n (fun v => ξ v / (Fx v : ℂ))
      (fun w => (Fy (-w) : ℂ) * conj (γ (-w)))‖ ≤ η +
      (∑' v : ℤ, (omittedEvent H₁ K n v).indicator (fun _ => (1 : ℝ)) ω *
        (‖ξ v‖ * ‖γ ((n : ℤ) + v)‖)) +
      (∑' v : ℤ, (omittedEvent H₂ K n v).indicator (fun _ => (1 : ℝ)) ω *
        (‖ξ v‖ * ‖γ ((n : ℤ) + v)‖)) := by
  classical
  have hmask (H : ℤ → Set Ω) (k : ℤ) :
      ({k | ω ∈ H k} : Set ℤ).indicator (fun _ => (1 : ℝ)) k =
        (H k).indicator (fun _ => (1 : ℝ)) ω := by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  have hdom := InvariantProjection.l2_masked_convolution_tail_selector
    (window K n) ξ γ (Equiv.addLeft (n : ℤ)) hξ hγ
    (fun v => Fy ((n : ℤ) + v) / Fx v)
    (fun v => ⟨(hratio v).1.le, (hratio v).2.1.trans (hratio v).2.2⟩)
    η hη {k | ω ∈ H₁ k} {k | ω ∈ H₂ k} (selector K n)
    (by
      change (∑' v : ℤ, ((Fy ((n : ℤ) + v) / Fx v : ℝ) : ℂ) * ξ v *
        conj (γ ((n : ℤ) + v))) = 0
      calc
        _ = ∑' v : ℤ, (ξ v / (Fx v : ℂ)) *
            ((Fy ((n : ℤ) + v) : ℂ) * conj (γ ((n : ℤ) + v))) := by
          apply tsum_congr
          intro v
          exact (InvariantProjection.convolution_coefficient_factorization Fx Fy
            (fun v => ξ v) (fun v => γ v) (n : ℤ) v).symm
        _ = 0 := hzero)
    (by
      intro v hv
      have hvw : ¬ (|v| ≤ (K : ℤ) ∧ |(n : ℤ) + v| ≤ (K : ℤ)) := by
        intro hw
        apply hv
        simp only [window, Finset.mem_filter, Finset.mem_Icc]
        exact ⟨abs_le.mp hw.1, hw.2⟩
      have hk := InvariantProjection.omitted_index_selector (K : ℤ) (n : ℤ) v hvw
      have hb := (InvariantProjection.omitted_index_ratio_bound (K : ℤ) (n : ℤ) v
        (fun k => Fy k / Fx k) _ (hratio v).2.1).trans (htail _ hk)
      simpa only [selector, hmask] using hb)
  simp only [hmask] at hdom
  rw [tsum_omittedEvent H₁ K n ω
    (fun v => ‖ξ v‖ * ‖γ ((Equiv.addLeft (n : ℤ)) v)‖),
    tsum_omittedEvent H₂ K n ω
    (fun v => ‖ξ v‖ * ‖γ ((Equiv.addLeft (n : ℤ)) v)‖)] at hdom
  convert hdom using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  change (ξ v / (Fx v : ℂ)) *
    ((Fy (-(-(n : ℤ) - v)) : ℂ) * conj (γ (-(-(n : ℤ) - v)))) = _
  have hsign : -(-(n : ℤ) - v) = (n : ℤ) + v := by omega
  rw [hsign]
  exact InvariantProjection.convolution_coefficient_factorization Fx Fy (fun v => ξ v) (fun v => γ v) (n : ℤ) v
  all_goals rfl

end InvariantProjection.ConditionalConvolution

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalMaskedTail
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal

namespace InvariantProjection

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem lintegral_tsum_masked_mul_le_of_condExp
    {ι : Type*} [mι : MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    [IsFiniteMeasure μ]
    {a b : Ω × ι → ℝ} (ha : Measurable a) (hb : Measurable b)
    (ha_nonneg : ∀ z, 0 ≤ a z) (hb_nonneg : ∀ z, 0 ≤ b z)
    {H : Set (Ω × ι)} (hH : MeasurableSet H)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {δ : ℝ} (hδ : 0 ≤ δ)
    (ha_endpoint : ∀ i, StronglyMeasurable[m] (fun ω => a (ω, i) ^ 2))
    (hcond : ∀ i, μ[({ω | (ω, i) ∈ H}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ)
    (ha_energy : (∫⁻ ω, ∑' i, ENNReal.ofReal (a (ω, i) ^ 2) ∂μ) ≤ 1)
    (hb_energy : (∫⁻ ω, ∑' i, ENNReal.ofReal (b (ω, i) ^ 2) ∂μ) ≤ 1) :
    (∫⁻ ω, ∑' i, H.indicator
      (fun z => ENNReal.ofReal (a z) * ENNReal.ofReal (b z)) (ω, i) ∂μ) ≤
      ENNReal.ofReal (Real.sqrt δ) := by
  have ha_sq_int : ∀ i, Integrable (fun ω => a (ω, i) ^ 2) μ := by
    intro i
    refine ⟨((ha.comp (@measurable_prodMk_right Ω ι mΩ mι i)).pow_const 2).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun _ => sq_nonneg _)).2
    calc
      (∫⁻ ω, ENNReal.ofReal (a (ω, i) ^ 2) ∂μ) ≤
          ∫⁻ ω, ∑' j, ENNReal.ofReal (a (ω, j) ^ 2) ∂μ :=
        lintegral_mono fun ω => ENNReal.le_tsum (f := fun j => ENNReal.ofReal (a (ω, j) ^ 2)) i
      _ ≤ 1 := ha_energy
      _ < ⊤ := by simp
  have hs : ∀ i, MeasurableSet[mΩ] {ω | (ω, i) ∈ H} := fun i =>
    hH.preimage (@measurable_prodMk_right Ω ι mΩ mι i)
  have hsmall := lintegral_tsum_indicator_le_of_condExp_indicator_le_of_energy_le_one
    (mΩ := mΩ) hm hs hδ ha_sq_int ha_endpoint
    (fun _ => Filter.Eventually.of_forall fun _ => sq_nonneg _) hcond ha_energy
  have hmasked : (∫⁻ ω, ∑' i, H.indicator
      (fun z => ENNReal.ofReal (a z) ^ (2 : ℕ)) (ω, i) ∂μ) ≤ ENNReal.ofReal δ := by
    convert hsmall using 1
    all_goals try with_reducible_and_instances rfl
    apply lintegral_congr
    intro ω
    apply tsum_congr
    intro i
    by_cases hi : (ω, i) ∈ H
    · simp [hi, ENNReal.ofReal_pow (ha_nonneg (ω, i))]
    · simp [hi]
  have hb2 : (∫⁻ ω, ∑' i, ENNReal.ofReal (b (ω, i)) ^ (2 : ℕ) ∂μ) ≤ 1 := by
    simpa only [← ENNReal.ofReal_pow (hb_nonneg _)] using hb_energy
  let : MeasurableSpace Ω := mΩ
  have hcs := Invariant233.MaskedTail.lintegral_tsum_indicator_mul_le_sqrt
    (μ := μ) hH ha.ennreal_ofReal.aemeasurable hb.ennreal_ofReal.aemeasurable hmasked hb2
  simpa only [ENNReal.ofReal_rpow_of_nonneg hδ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← Real.sqrt_eq_rpow] using hcs

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalL2Tail
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal lp

namespace InvariantProjection

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}

theorem l2_tsum_ofReal_sq (x : ℓ²(ℤ, ℂ)) :
    (∑' i : ℤ, ENNReal.ofReal (‖x i‖ ^ 2)) = ENNReal.ofReal (‖x‖ ^ 2) := by
  have hs : HasSum (fun i : ℤ => ‖x i‖ ^ 2) (‖x‖ ^ 2) := by
    simpa using lp.hasSum_norm (p := (2 : ℝ≥0∞)) (by norm_num) x
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) hs.summable, hs.tsum_eq]

theorem lintegral_l2_sq_le_one [IsProbabilityMeasure μ]
    (ξ : Ω → ℓ²(ℤ, ℂ)) (hξ : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1) :
    (∫⁻ ω, ∑' i : ℤ, ENNReal.ofReal (‖ξ ω i‖ ^ 2) ∂μ) ≤ 1 := by
  calc
    _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hξ] with ω hω
      rw [l2_tsum_ofReal_sq]
      apply ENNReal.ofReal_le_one.mpr
      nlinarith [norm_nonneg (ξ ω)]
    _ = 1 := by simp

theorem lintegral_l2_masked_tail_le_of_condExp
    [IsProbabilityMeasure μ]
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (hγ : StronglyMeasurable γ)
    (hξ_ball : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1) (hγ_ball : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ 1)
    (e : ℤ ≃ ℤ) {H : Set (Ω × ℤ)} (hH : MeasurableSet H)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hξ : StronglyMeasurable[m] ξ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcond : ∀ i : ℤ, μ[({ω | (ω, i) ∈ H}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ) :
    (∫⁻ ω, ∑' i : ℤ, H.indicator
      (fun z => ENNReal.ofReal ‖ξ z.1 z.2‖ * ENNReal.ofReal ‖γ z.1 (e z.2)‖)
      (ω, i) ∂μ) ≤ ENNReal.ofReal (Real.sqrt δ) := by
  let : MeasurableSpace Ω := mΩ
  have hxcoord (i : ℤ) : StronglyMeasurable[m] (fun ω => ξ ω i) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 i).continuous.comp_stronglyMeasurable hξ
  have hycoord (i : ℤ) : StronglyMeasurable (fun ω => γ ω (e i)) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (e i)).continuous.comp_stronglyMeasurable hγ
  apply lintegral_tsum_masked_mul_le_of_condExp
    (a := fun z : Ω × ℤ => ‖ξ z.1 z.2‖)
    (b := fun z : Ω × ℤ => ‖γ z.1 (e z.2)‖)
    (measurable_from_prod_countable_left fun i => ((hxcoord i).mono hm).norm.measurable)
    (measurable_from_prod_countable_left fun i => (hycoord i).norm.measurable)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hH hm hδ
    (fun i => (hxcoord i).norm.pow 2) hcond
  · exact lintegral_l2_sq_le_one ξ hξ_ball
  · have h := lintegral_l2_sq_le_one γ hγ_ball
    calc
      _ = ∫⁻ ω, ∑' i : ℤ, ENNReal.ofReal (‖γ ω i‖ ^ 2) ∂μ := by
        apply lintegral_congr
        intro ω
        exact e.tsum_eq (fun i => ENNReal.ofReal (‖γ ω i‖ ^ 2))
      _ ≤ 1 := h

theorem integral_l2_masked_tail_le_of_condExp
    [IsProbabilityMeasure μ]
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (hγ : StronglyMeasurable γ)
    (hξ_ball : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1) (hγ_ball : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ 1)
    (e : ℤ ≃ ℤ) {H : Set (Ω × ℤ)} (hH : MeasurableSet H)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hξ : StronglyMeasurable[m] ξ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcond : ∀ i : ℤ, μ[({ω | (ω, i) ∈ H}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ) :
    (∀ᵐ ω ∂μ, Summable (fun i : ℤ => H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i))) ∧
    Integrable (fun ω => ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i)) μ ∧
    (∫ ω, ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i) ∂μ) ≤ Real.sqrt δ := by
  let : MeasurableSpace Ω := mΩ
  have hbound := lintegral_l2_masked_tail_le_of_condExp
    (mΩ := mΩ) ξ γ hγ hξ_ball hγ_ball e hH hm hξ hδ hcond
  have hxcoord (i : ℤ) : StronglyMeasurable (fun ω => ξ ω i) :=
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 i).continuous.comp_stronglyMeasurable hξ).mono hm
  have hycoord (i : ℤ) : StronglyMeasurable (fun ω => γ ω (e i)) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (e i)).continuous.comp_stronglyMeasurable hγ
  have hf (i : ℤ) : Measurable (fun ω => H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i)) := by
    have hs := hH.preimage (@measurable_prodMk_right Ω ℤ mΩ inferInstance i)
    convert (((hxcoord i).norm.measurable.mul (hycoord i).norm.measurable).indicator hs) using 1
    all_goals try with_reducible_and_instances rfl
    funext ω
    by_cases hi : (ω, i) ∈ H <;> simp [hi]
  apply Invariant233.MaskedTail.real_tsum_integrable_of_lintegral_bound hf
    (fun i ω => Set.indicator_nonneg (fun z _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) (ω, i))
    (Real.sqrt_nonneg δ)
  convert hbound using 1
  all_goals try with_reducible_and_instances rfl
  apply lintegral_congr
  intro ω
  apply tsum_congr
  intro i
  by_cases hi : (ω, i) ∈ H
  · simp [hi, ENNReal.ofReal_mul (norm_nonneg _)]
  · simp [hi]

theorem integral_l2_masked_tail_le_of_condExp_right
    [IsProbabilityMeasure μ]
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (hξ : StronglyMeasurable ξ)
    (hξ_ball : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ 1) (hγ_ball : ∀ᵐ ω ∂μ, ‖γ ω‖ ≤ 1)
    (e : ℤ ≃ ℤ) {H : Set (Ω × ℤ)} (hH : MeasurableSet H)
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) (hγ : StronglyMeasurable[m] γ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcond : ∀ i : ℤ, μ[({ω | (ω, i) ∈ H}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ) :
    Integrable (fun ω => ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i)) μ ∧
    (∫ ω, ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i) ∂μ) ≤ Real.sqrt δ := by
  let : MeasurableSpace Ω := mΩ
  let H' : Set (Ω × ℤ) := {z | (z.1, e.symm z.2) ∈ H}
  have hH' : MeasurableSet H' :=
    hH.preimage (measurable_fst.prodMk ((measurable_of_countable e.symm).comp measurable_snd))
  have hc' : ∀ j : ℤ, μ[({ω | (ω, j) ∈ H'}).indicator (fun _ => (1 : ℝ)) | m]
      ≤ᵐ[μ] fun _ => δ := fun j => hcond (e.symm j)
  have h := integral_l2_masked_tail_le_of_condExp (mΩ := mΩ)
    γ ξ hξ hγ_ball hξ_ball e.symm hH' hm hγ hδ hc'
  have heq : (fun ω => ∑' i : ℤ, H.indicator
      (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 (e z.2)‖) (ω, i)) =
      (fun ω => ∑' j : ℤ, H'.indicator
      (fun z => ‖γ z.1 z.2‖ * ‖ξ z.1 (e.symm z.2)‖) (ω, j)) := by
    funext ω
    rw [← e.tsum_eq (fun j => H'.indicator
      (fun z => ‖γ z.1 z.2‖ * ‖ξ z.1 (e.symm z.2)‖) (ω, j))]
    apply tsum_congr
    intro i
    by_cases hi : (ω, i) ∈ H <;> simp [H', hi, mul_comm]
  rw [heq]
  exact h.2

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ConditionalConvolution
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal lp ComplexConjugate

noncomputable section

namespace InvariantProjection.ConditionalConvolution

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
variable {K : ℕ} {D a c η δ : ℝ}

omit mΩ in
theorem exceptionalTail_nonneg (H : ℤ → Set Ω) (K n : ℕ)
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (ω : Ω) :
    0 ≤ exceptionalTail H K n ξ γ ω := by
  apply tsum_nonneg
  intro v
  exact Set.indicator_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ω

omit mΩ in
theorem exceptionalTail_eq_productMask (H : ℤ → Set Ω) (K n : ℕ)
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) :
    exceptionalTail H K n ξ γ = fun ω => ∑' v : ℤ,
      ({z : Ω × ℤ | z.1 ∈ omittedEvent H K n z.2}).indicator
        (fun z => ‖ξ z.1 z.2‖ * ‖γ z.1 ((n : ℤ) + z.2)‖) (ω, v) := by
  funext ω
  unfold exceptionalTail
  apply tsum_congr
  intro v
  by_cases hv : ω ∈ omittedEvent H K n v <;> simp [hv]

omit mΩ in
theorem exceptionalTail_eq_indicatorOne (H : ℤ → Set Ω) (K n : ℕ)
    (ξ γ : Ω → ℓ²(ℤ, ℂ)) (ω : Ω) :
    exceptionalTail H K n ξ γ ω = ∑' v : ℤ,
      (omittedEvent H K n v).indicator (fun _ => (1 : ℝ)) ω *
        (‖ξ ω v‖ * ‖γ ω ((n : ℤ) + v)‖) := by
  unfold exceptionalTail
  apply tsum_congr
  intro v
  by_cases hv : ω ∈ omittedEvent H K n v <;> simp [hv]

namespace Data

variable (d : Data Ω μ K D a c η δ)

theorem coeffA_measurable (v : ℤ) : Measurable (fun ω => coeffA d.ξ d.Fx ω v) := by
  have hx : StronglyMeasurable (fun ω => d.ξ ω v) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 v).continuous.comp_stronglyMeasurable
      (d.ξ_measurable.mono d.mX_le)
  exact hx.measurable.div (Complex.continuous_ofReal.measurable.comp (d.Fx_measurable v))

theorem coeffB_measurable (v : ℤ) : Measurable (fun ω => coeffB d.γ d.Fy ω v) := by
  have hy : StronglyMeasurable (fun ω => d.γ ω (-v)) :=
    (lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (-v)).continuous.comp_stronglyMeasurable
      (d.γ_measurable.mono d.mY_le)
  exact (Complex.continuous_ofReal.measurable.comp (d.Fy_measurable (-v))).mul
    (Complex.continuous_conj.measurable.comp hy.measurable)

theorem integrableOn_norm_truncated [IsFiniteMeasure μ] (n : ℕ) :
    IntegrableOn (fun ω => ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖) d.E μ := by
  exact Invariant233.FiniteWindow.integrableOn_norm_convolution μ d.E
    (measure_lt_top μ d.E) K n D (coeffA d.ξ d.Fx) (coeffB d.γ d.Fy)
    d.coeffA_measurable d.coeffB_measurable
    (d.coefficient_bounds.mono fun _ h => h.1)
    (d.coefficient_bounds.mono fun _ h => h.2.1)

theorem first_tail_bound [IsProbabilityMeasure μ] (n : ℕ) (hδ : 0 ≤ δ) :
    Integrable (exceptionalTail d.H₁ K n d.ξ d.γ) μ ∧
    (∫ ω, exceptionalTail d.H₁ K n d.ξ d.γ ω ∂μ) ≤ Real.sqrt δ := by
  have h := integral_l2_masked_tail_le_of_condExp (mΩ := mΩ)
    d.ξ d.γ (d.γ_measurable.mono d.mY_le) d.ξ_unit d.γ_unit
    (Equiv.addLeft (n : ℤ))
    (measurableSet_omittedMask d.H₁ K n (fun k _ => d.H₁_measurable k))
    d.mX_le d.ξ_measurable hδ
    (condExp_omittedMask_section_le μ d.mX d.H₁ K n hδ d.conditional₁)
  rw [exceptionalTail_eq_productMask]
  exact h.2

theorem second_tail_bound [IsProbabilityMeasure μ] (n : ℕ) (hδ : 0 ≤ δ) :
    Integrable (exceptionalTail d.H₂ K n d.ξ d.γ) μ ∧
    (∫ ω, exceptionalTail d.H₂ K n d.ξ d.γ ω ∂μ) ≤ Real.sqrt δ := by
  have h := integral_l2_masked_tail_le_of_condExp_right (mΩ := mΩ)
    d.ξ d.γ (d.ξ_measurable.mono d.mX_le) d.ξ_unit d.γ_unit
    (Equiv.addLeft (n : ℤ))
    (measurableSet_omittedMask d.H₂ K n (fun k _ => d.H₂_measurable k))
    d.mY_le d.γ_measurable hδ
    (condExp_omittedMask_section_le μ d.mY d.H₂ K n hδ d.conditional₂)
  rw [exceptionalTail_eq_productMask]
  exact h

theorem integral_truncated_le_of_pointwise [IsProbabilityMeasure μ]
    (n : ℕ) (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hpoint : ∀ᵐ ω ∂μ.restrict d.E,
      ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖ ≤
        η + exceptionalTail d.H₁ K n d.ξ d.γ ω + exceptionalTail d.H₂ K n d.ξ d.γ ω) :
    (∫ ω in d.E, ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖ ∂μ) ≤
      η + 2 * Real.sqrt δ := by
  obtain ⟨ht₁, hb₁⟩ := d.first_tail_bound n hδ
  obtain ⟨ht₂, hb₂⟩ := d.second_tail_bound n hδ
  have hi : Integrable (d.E.indicator (fun ω =>
      ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖)) μ :=
    (integrable_indicator_iff d.E_measurable).mpr (d.integrableOn_norm_truncated n)
  have hfull : ∀ᵐ ω ∂μ,
      d.E.indicator (fun ω => ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖) ω ≤
      η + exceptionalTail d.H₁ K n d.ξ d.γ ω + exceptionalTail d.H₂ K n d.ξ d.γ ω := by
    filter_upwards [(ae_restrict_iff' d.E_measurable).mp hpoint] with ω hω
    by_cases hE : ω ∈ d.E
    · simpa only [Set.indicator_of_mem hE] using hω hE
    · rw [Set.indicator_of_notMem hE]
      exact add_nonneg (add_nonneg hη (exceptionalTail_nonneg _ _ _ _ _ _))
        (exceptionalTail_nonneg _ _ _ _ _ _)
  have hiR := ((integrable_const η).add ht₁).add ht₂
  have hbound := integral_mono_ae hi hiR hfull
  rw [integral_indicator d.E_measurable] at hbound
  have heval : (∫ ω, ((fun _ : Ω => η) + exceptionalTail d.H₁ K n d.ξ d.γ +
      exceptionalTail d.H₂ K n d.ξ d.γ) ω ∂μ) =
      η + (∫ ω, exceptionalTail d.H₁ K n d.ξ d.γ ω ∂μ) +
      (∫ ω, exceptionalTail d.H₂ K n d.ξ d.γ ω ∂μ) := by
    calc
      _ = (∫ ω, ((fun _ : Ω => η) + exceptionalTail d.H₁ K n d.ξ d.γ) ω ∂μ) +
          ∫ ω, exceptionalTail d.H₂ K n d.ξ d.γ ω ∂μ :=
        integral_add ((integrable_const η).add ht₁) ht₂
      _ = ((∫ _ : Ω, η ∂μ) + ∫ ω, exceptionalTail d.H₁ K n d.ξ d.γ ω ∂μ) +
          ∫ ω, exceptionalTail d.H₂ K n d.ξ d.γ ω ∂μ := by
        rw [show (∫ ω, ((fun _ : Ω => η) + exceptionalTail d.H₁ K n d.ξ d.γ) ω ∂μ) =
          (∫ _ : Ω, η ∂μ) + ∫ ω, exceptionalTail d.H₁ K n d.ξ d.γ ω ∂μ from
          integral_add (integrable_const η) ht₁]
      _ = _ := by simp
  rw [heval] at hbound
  linarith

theorem pointwise_truncated_bound (n : ℕ) (hn : n ≤ 2 * K) (hη : 0 ≤ η) :
    ∀ᵐ ω ∂μ.restrict d.E,
      ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖ ≤
        η + exceptionalTail d.H₁ K n d.ξ d.γ ω + exceptionalTail d.H₂ K n d.ξ d.γ ω := by
  filter_upwards [ae_restrict_of_ae d.ξ_unit, ae_restrict_of_ae d.γ_unit,
    ae_restrict_of_ae (d.ratio_bounds n hn), ae_restrict_of_ae (d.zero_convolution n hn),
    d.attenuation] with ω hξ hγ hr hz ht
  have hz' : (∑' v : ℤ, (d.ξ ω v / (d.Fx ω v : ℂ)) *
      ((d.Fy ω ((n : ℤ) + v) : ℂ) * conj (d.γ ω ((n : ℤ) + v)))) = 0 := by
    simpa only [coeffA, coeffB, neg_sub, neg_neg, sub_neg_eq_add, add_comm] using hz
  have h := pointwise_bound K n (d.Fx ω) (d.Fy ω) (d.ξ ω) (d.γ ω)
    hξ hγ η hη d.H₁ d.H₂ ω hr hz' ht
  rw [← exceptionalTail_eq_indicatorOne, ← exceptionalTail_eq_indicatorOne] at h
  exact h

theorem obstruction_of_pointwise [IsProbabilityMeasure μ]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcoeff : ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖A v‖ ≤ D) →
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖B v‖ ≤ D) →
      a ≤ ‖A 0‖ → a ≤ ‖B 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖truncated K n A B‖)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ)
    (hpoint : ∀ n : ℕ, n ≤ 2 * K → ∀ᵐ ω ∂μ.restrict d.E,
      ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖ ≤
        η + exceptionalTail d.H₁ K n d.ξ d.γ ω + exceptionalTail d.H₂ K n d.ξ d.γ ω) :
    c * ε ≤ ((2 * K + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  apply Invariant233.FiniteWindow.finite_sum_obstruction μ d.E (2 * K + 1)
    (fun n ω => ‖truncated K n (coeffA d.ξ d.Fx ω) (coeffB d.γ d.Fy ω)‖)
    c ε (η + 2 * Real.sqrt δ) hε d.E_mass
  · intro n _
    exact d.integrableOn_norm_truncated n
  · exact Invariant233.FiniteWindow.integral_lower_of_sum_bound μ K D a ε hcoeff
      d.E (coeffA d.ξ d.Fx) (coeffB d.γ d.Fy)
      d.coeffA_measurable d.coeffB_measurable d.coefficient_bounds
  · intro n hn
    exact d.integral_truncated_le_of_pointwise n hη hδ
      (hpoint n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)))

end Data

end InvariantProjection.ConditionalConvolution

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleObstruction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Filter
open InvariantProjection.ConditionalConvolution

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

include hp

theorem convolution_sum_lower (j : ℕ) (hj : 1 ≤ j) :
    ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) → ‖A v‖ ≤ p.coefficientBound j) →
      (∀ v : ℤ, |v| ≤ (p.K j : ℤ) → ‖B v‖ ≤ p.coefficientBound j) →
      1 / (j : ℝ) ≤ ‖A 0‖ → 1 / (j : ℝ) ≤ ‖B 0‖ →
      p.ε j ≤ ∑ n ∈ Finset.range (2 * p.K j + 1),
        ‖truncated (p.K j) n A B‖ := by
  apply FiniteWindow.convolution_sum_lower_bound_of_supported_bound
    (p.K j) (p.coefficientBound j) (1 / (j : ℝ)) (p.ε j)
  simpa only [CircleParameterData.convolutionCoefficient] using hp.polynomial_lower j hj

theorem conditional_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (j : ℕ) (hj : 1 ≤ j) {c η δ : ℝ}
    (d : Data Ω μ (p.K j) (p.coefficientBound j) (1 / (j : ℝ)) c η δ)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) :
    c * p.ε j ≤ ((2 * p.K j + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  exact d.obstruction_of_pointwise (hp.epsilon_pos j hj).le
    (hp.convolution_sum_lower j hj) hη hδ
    (fun n hn => d.pointwise_truncated_bound n hn hη)

theorem no_conditional_data_at_stage {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (j : ℕ) (hj : 1 ≤ j) (c : ℝ) (hc : 1 / (j : ℝ) < c) :
    ¬ Nonempty (Data Ω μ (p.K j) (p.coefficientBound j) (1 / (j : ℝ)) c
      (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  rintro ⟨d⟩
  have hbound := hp.conditional_bound j hj d
    (Real.exp_pos _).le (Real.exp_pos _).le
  have hchoice := hp.polynomial_attenuation j hj
  have htail := ConvolutionContradiction.coefficient_tail_le
    (p.K j) (p.L j) (p.ε j) (j : ℝ) (hp.L_pos j hj).le
    (by simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
      Nat.cast_ofNat] using hchoice)
  apply ConvolutionContradiction.fixed_stage_contradiction c (p.ε j) (j : ℝ)
    (hp.epsilon_pos j hj) hc
  apply le_trans ?_ htail
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_one,
    Nat.cast_ofNat] using hbound

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ParameterCircleReindex
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem coord_to_nat_bijective :
    Bijective (fun i : p.Coord => (i.2 : ℕ) - 1) := by
  have hpos (a : p.Coord) : 1 ≤ (a.2 : ℕ) := by
    have h := (p.mem_block_iff (a.1 + 1) a.2).mp a.2.property
    omega
  constructor
  · rintro ⟨j, i, hi⟩ ⟨k, l, hl⟩ h
    have hip := hpos ⟨j, i, hi⟩
    have hlp := hpos ⟨k, l, hl⟩
    change 1 ≤ i at hip
    change 1 ≤ l at hlp
    have hil : i = l := by change i - 1 = l - 1 at h; omega
    subst l
    have hjk := p.block_index_unique hp.m_pos hi hl
    have hjk' : j = k := by omega
    subst k
    rfl
  · intro n
    obtain ⟨j, hj, hn⟩ := p.exists_mem_block hp.m_pos (n + 1) (by omega)
    refine ⟨⟨j - 1, ⟨n + 1, ?_⟩⟩, by simp⟩
    simpa only [Nat.sub_add_cancel hj] using hn

theorem parameter_cocycle_eq_flattened (k : ℤ) (x : Circle) :
    p.floorCocycle θ k x =
      CircleWeights.cocycle θ p.flattenedFrequency p.flattenedCost k x := by
  let e : p.Coord ≃ ℕ := Equiv.ofBijective _ hp.coord_to_nat_bijective
  have hindex (i : p.Coord) : e i + 1 = (i.2 : ℕ) := by
    have hi := (p.mem_block_iff (i.1 + 1) i.2).mp i.2.property
    change (i.2 : ℕ) - 1 + 1 = (i.2 : ℕ)
    omega
  have hfreq (i : p.Coord) : p.flattenedFrequency (e i) = p.coordFrequency i := by
    simp only [CircleParameterData.flattenedFrequency, CircleParameterData.coordFrequency,
      hindex i]
  have hcost (i : p.Coord) : p.flattenedCost (e i) = p.coordCost i := by
    apply p.flattenedCost_eq_of_mem hp.m_pos
    simpa only [hindex i] using i.2.property
  unfold CircleParameterData.floorCocycle CircleWeights.cocycle CircleWeights.floorCost
  congr 2
  calc
    (∑' i : p.Coord, p.coordCost i *
        (Int.floor (CircleWeights.coordinate p.coordFrequency i x +
          (k : ℝ) * CircleWeights.phase θ p.coordFrequency i) : ℝ)) =
        ∑' i : p.Coord, p.flattenedCost (e i) *
          (Int.floor (CircleWeights.coordinate p.flattenedFrequency (e i) x +
            (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency (e i)) : ℝ) := by
      apply tsum_congr
      intro i
      simp only [hcost, CircleWeights.coordinate, CircleWeights.phase, hfreq]
    _ = ∑' n : ℕ, p.flattenedCost n *
        (Int.floor (CircleWeights.coordinate p.flattenedFrequency n x +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency n) : ℝ) :=
      e.tsum_eq (fun n : ℕ => p.flattenedCost n *
        (Int.floor (CircleWeights.coordinate p.flattenedFrequency n x +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency n) : ℝ))

end Invariant233.CircleParameterLaws

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadix
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.MixedRadix.hybrid_apply_ge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem sum_terms_le_reciprocal_gap {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j N : ℕ) :
    (∑ n ∈ Finset.range N, term d (j + n)) ≤
      1 / (denominator r j : ℝ) - 1 / (denominator r (j + N) : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hterm := term_le_reciprocal_gap hr d (j + N)
      simp only [Nat.add_assoc] at hterm
      linarith

theorem summable_terms {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) :
    Summable (term d) := by
  apply summable_of_sum_range_le (term_nonneg d) (c := 1)
  intro N
  have h := sum_terms_le_reciprocal_gap hr d 0 N
  simp only [Nat.zero_add, denominator_zero, Nat.cast_one, div_one] at h
  have hnonneg : (0 : ℝ) ≤ 1 / (denominator r N : ℝ) := by positivity
  linarith

theorem tsum_tail_le {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    (∑' n, term d (j + n)) ≤ 1 / (denominator r j : ℝ) := by
  apply Real.tsum_le_of_sum_range_le (fun n => term_nonneg d (j + n))
  intro N
  have h := sum_terms_le_reciprocal_gap hr d j N
  have hnonneg : (0 : ℝ) ≤ 1 / (denominator r (j + N) : ℝ) := by positivity
  linarith

theorem tailValue_nonneg {r : ℕ → ℕ} (d : Digits r) (j : ℕ) :
    0 ≤ tailValue d j := by
  unfold tailValue
  exact mul_nonneg (Nat.cast_nonneg _) (tsum_nonneg (fun n => term_nonneg d (j + n)))

theorem tailValue_le_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    tailValue d j ≤ 1 := by
  have hq : (0 : ℝ) < denominator r j := by exact_mod_cast denominator_pos hr j
  calc
    tailValue d j ≤ (denominator r j : ℝ) * (1 / (denominator r j : ℝ)) :=
      mul_le_mul_of_nonneg_left (tsum_tail_le hr d j) hq.le
    _ = 1 := by field_simp

theorem tailValue_rec {r : ℕ → ℕ} (hr : ∀ n, 0 < r n) (d : Digits r) (j : ℕ) :
    tailValue d j = ((d j : ℝ) + tailValue d (j + 1)) / (r j : ℝ) := by
  have hs : Summable (fun n => term d (j + (n + 1))) :=
    (summable_terms hr d).comp_injective (fun _ _ h => by omega)
  have hsplit : (∑' n, term d (j + n)) =
      term d j + ∑' n, term d (j + 1 + n) := by
    simpa only [Nat.add_zero, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
      using tsum_eq_zero_add' (f := fun n => term d (j + n)) hs
  have hq : (denominator r j : ℝ) ≠ 0 :=
    ne_of_gt (by exact_mod_cast denominator_pos hr j)
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  unfold tailValue
  rw [hsplit]
  simp only [term, denominator_succ, Nat.cast_mul]
  field_simp

theorem abs_tailValue_sub_raw_le {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j : ℕ) {X : ℝ}
    (hlo : (d j : ℝ) ≤ (r j : ℝ) * X)
    (hhi : (r j : ℝ) * X ≤ (d j : ℝ) + 1) :
    |tailValue d j - X| ≤ 1 / (r j : ℝ) := by
  have hrr : (0 : ℝ) < r j := by exact_mod_cast hr j
  have hrec := tailValue_rec hr d j
  have heq : (r j : ℝ) * tailValue d j = (d j : ℝ) + tailValue d (j + 1) := by
    rw [hrec]
    field_simp
  rw [abs_sub_le_iff]
  constructor
  · apply (le_div_iff₀ hrr).mpr
    nlinarith [tailValue_le_one hr d (j + 1)]
  · apply (le_div_iff₀ hrr).mpr
    nlinarith [tailValue_nonneg d (j + 1)]

theorem abs_tailValue_sub_raw_le_of_floor {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hdigit : ⌊(r j : ℝ) * X⌋₊ = (d j : ℕ)) :
    |tailValue d j - X| ≤ 1 / (r j : ℝ) := by
  have h := (Nat.floor_eq_iff (mul_nonneg (Nat.cast_nonneg _) hX)).mp hdigit
  exact abs_tailValue_sub_raw_le hr d j h.1 h.2.le

theorem ofDigits_eq_prefix_add_tail {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    ofDigits d = (∑ n ∈ Finset.range N, term d n) + ∑' n, term d (N + n) := by
  simpa only [ofDigits, Nat.add_comm] using
    ((summable_terms hr d).sum_add_tsum_nat_add N).symm

theorem denominator_mul_prefix {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * (∑ n ∈ Finset.range N, term d n) = (prefixRank d N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hq : (denominator r N : ℝ) ≠ 0 :=
        ne_of_gt (by exact_mod_cast denominator_pos hr N)
      have hrr : (r N : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr N)
      rw [Finset.sum_range_succ, prefixRank_succ, Nat.cast_add, Nat.cast_mul]
      simp only [term, denominator_succ, Nat.cast_mul] at *
      field_simp at *
      nlinarith

theorem denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (N : ℕ) :
    (denominator r N : ℝ) * ofDigits d = (prefixRank d N : ℝ) + tailValue d N := by
  rw [ofDigits_eq_prefix_add_tail hr d N, mul_add, denominator_mul_prefix hr d N]
  rfl

theorem tailValue_eq_one_imp_next {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (j : ℕ) (heq : tailValue d j = 1) :
    tailValue d (j + 1) = 1 := by
  have hrr : (r j : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr j)
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d j)
  have hd : (d j : ℝ) + 1 ≤ (r j : ℝ) := by exact_mod_cast (d j).isLt
  rw [heq, one_mul] at hrec
  linarith [tailValue_le_one hr d (j + 1)]

theorem tailValue_lt_one {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) : tailValue d j < 1 := by
  by_contra hnot
  have heq : tailValue d j = 1 := le_antisymm (tailValue_le_one hr d j) (le_of_not_gt hnot)
  have hprop : ∀ k, tailValue d (j + k) = 1 := by
    intro k
    induction k with
    | zero => simpa using heq
    | succ k ih =>
        simpa only [Nat.add_assoc] using tailValue_eq_one_imp_next hr d (j + k) ih
  obtain ⟨n, hjn, hn⟩ := hnt j
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hjn
  have hrr : (r (j + k) : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hr (j + k))
  have hrec := (eq_div_iff hrr).mp (tailValue_rec hr d (j + k))
  rw [hprop k, one_mul] at hrec
  have hd : (d (j + k) : ℝ) + 1 < (r (j + k) : ℝ) := by exact_mod_cast hn
  linarith [tailValue_le_one hr d (j + k + 1)]

theorem fract_denominator_mul_ofDigits {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (d : Digits r) (hnt : Nonterminal d) (j : ℕ) :
    Int.fract ((denominator r j : ℝ) * ofDigits d) = tailValue d j := by
  rw [denominator_mul_ofDigits hr d j, Int.fract_natCast_add]
  exact Int.fract_eq_self.mpr ⟨tailValue_nonneg d j, tailValue_lt_one hr d hnt j⟩

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

theorem denominator_radices {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hdiv : ∀ n, q n ∣ q (n + 1)) (N : ℕ) : denominator (radices q) N = q N := by
  induction N with
  | zero => simpa using hq0.symm
  | succ N ih =>
      rw [denominator_succ, ih, radices]
      exact Nat.mul_div_cancel' (hdiv N)

theorem radices_pos {q : ℕ → ℕ} (hq : ∀ n, 0 < q n)
    (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1)) (n : ℕ) :
    0 < radices q n := lt_of_lt_of_le (by decide) (radices_ge_two hq hstrict hdiv n)

theorem coordinate_eq_tailValue {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hq : ∀ n, 0 < q n) (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1))
    (d : Digits (radices q)) (hnt : Nonterminal d) (i : ℕ) :
    Int.fract ((q i : ℝ) * ofDigits d) = tailValue d i := by
  rw [← denominator_radices hq0 hdiv i]
  exact fract_denominator_mul_ofDigits (radices_pos hq hstrict hdiv) d hnt i

theorem abs_coordinate_sub_raw_le {q : ℕ → ℕ} (hq0 : q 0 = 1)
    (hq : ∀ n, 0 < q n) (hstrict : StrictMono q) (hdiv : ∀ n, q n ∣ q (n + 1))
    (d : Digits (radices q)) (hnt : Nonterminal d) (i : ℕ) {X : ℝ} (hX : 0 ≤ X)
    (hfloor : ⌊(radices q i : ℝ) * X⌋₊ = (d i : ℕ)) :
    |Int.fract ((q i : ℝ) * ofDigits d) - X| ≤ 1 / (radices q i : ℝ) := by
  rw [coordinate_eq_tailValue hq0 hq hstrict hdiv d hnt i]
  exact abs_tailValue_sub_raw_le_of_floor (radices_pos hq hstrict hdiv) d i hX hfloor

@[simp] theorem hybrid_apply_lt {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : n < N) :
    hybrid d e N n = e n := ite_eq_left hn

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingParameters
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma coupling_K_ge (j : ℕ) (hj : 1 ≤ j) : 100 ≤ p.K j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction n with
  | zero => simpa using hp.initial_K.ge
  | succ n ih =>
    have h := hp.K_double (1 + n) (by omega)
    have he : 1 + (n + 1) = 1 + n + 1 := by omega
    rw [he]
    omega

lemma coupling_radix_ge_N {s i : ℕ} (hs : 1 ≤ s) (hi : i ∈ p.block s) :
    p.N s ≤ (MixedRadix.radices p.q i : ℝ) := by
  simpa only [MixedRadix.radices, Nat.cast_div (hp.frequency_divisible i)
    (by exact_mod_cast (Nat.ne_of_gt (hp.q_pos i)) : (p.q i : ℝ) ≠ 0)] using hp.frequency_ratios s hs i hi

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMarginalBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped BigOperators ENNReal

namespace Invariant233.CouplingMarginalBounds

lemma rho_div_width_le {κ m w : ℝ} (hκ : 0 ≤ κ)
    (hm : 0 < m) (hw : 1 / m ≤ w) : rho κ m w / w ≤ κ := by
  exact (div_le_iff₀ (width_pos hm hw)).2 (rho_le_mul_width hκ hm hw)

end Invariant233.CouplingMarginalBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CouplingMixture
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

namespace Invariant233.CouplingMixture

variable {X I : Type*} [MeasurableSpace X] [Fintype I]

lemma withDensity_finite_mixture (μ : Measure X) (q : ℝ≥0∞)
    (p : I → ℝ≥0∞) (g : I → X → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    μ.withDensity (fun x => q + ∑ i, p i * g i x) =
      q • μ + ∑ i, p i • μ.withDensity (g i) := by
  classical
  have hsum : μ.withDensity (fun x => ∑ i, p i * g i x) =
      ∑ i, p i • μ.withDensity (g i) := by
    have hfin : ∀ s : Finset I, μ.withDensity (fun x => ∑ i ∈ s, p i * g i x) =
        ∑ i ∈ s, p i • μ.withDensity (g i) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert a s ha ih =>
        simp only [Finset.sum_insert ha]
        rw [show (fun x => p a * g a x + ∑ i ∈ s, p i * g i x) =
          (fun x => p a * g a x) + (fun x => ∑ i ∈ s, p i * g i x) from rfl,
          withDensity_add_left (show Measurable (fun x => p a * g a x) from measurable_const.mul (hg a)), ih]
        congr 1
        exact withDensity_smul (p a) (hg a)
    exact hfin Finset.univ
  rw [show (fun x => q + ∑ i, p i * g i x) =
    (fun _ => q) + (fun x => ∑ i, p i * g i x) from rfl,
    withDensity_add_left measurable_const, withDensity_const, hsum]

lemma intervalLaw_ae_mem (a b : ℝ) : ∀ᵐ x ∂intervalLaw a b, x ∈ Ico a b :=
  ae_cond_mem measurableSet_Ico

lemma cond_eq_withDensity_uniformDensity {μ : Measure X} [IsFiniteMeasure μ]
    {s : Set X} (hs : MeasurableSet s) (hpos : 0 < μ.real s) :
    μ[|s] = μ.withDensity (fun x =>
      ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) := by
  have hc : ENNReal.ofReal ((μ.real s)⁻¹) = (μ s)⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hpos, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top μ s)]
  have hfun : (fun x => ENNReal.ofReal (CouplingMarginalBounds.uniformDensity μ s x)) =
      s.indicator (fun _ => (μ s)⁻¹) := by
    ext x
    by_cases hx : x ∈ s <;> simp [CouplingMarginalBounds.uniformDensity, hx, hc]
  rw [hfun, withDensity_indicator hs, withDensity_const]
  rfl

omit [MeasurableSpace X] in
lemma ofReal_mixture_density (q : ℝ) (p : I → ℝ) (g : I → X → ℝ)
    (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i) (hg : ∀ i x, 0 ≤ g i x) (x : X) :
    ENNReal.ofReal (q + ∑ i, p i * g i x) =
      ENNReal.ofReal q + ∑ i, ENNReal.ofReal (p i) * ENNReal.ofReal (g i x) := by
  rw [ENNReal.ofReal_add hq (Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))),
    ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hp i) (hg i x))]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => ENNReal.ofReal_mul (hp i))

end Invariant233.CouplingMixture

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_OneCoordinateCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma baseLaw_eq_restrict : baseLaw = volume.restrict (Ico (0 : ℝ) 1) := by
  simp [baseLaw, intervalLaw, ProbabilityTheory.cond, Real.volume_Ico]

lemma interval_subset_unit {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Ico a b ⊆ Ico (0 : ℝ) 1 := by
  intro x hx
  exact ⟨ha.trans hx.1, hx.2.trans_le hb⟩

lemma baseLaw_interval_measure {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a ≤ b) :
    baseLaw.real (Ico a b) = b - a := by
  rw [measureReal_def, baseLaw_eq_restrict, Measure.restrict_apply measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb), Real.volume_Ico,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

lemma intervalLaw_eq_base_cond {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    intervalLaw a b = baseLaw[|Ico a b] := by
  rw [baseLaw_eq_restrict]
  simp only [intervalLaw, ProbabilityTheory.cond,
    Measure.restrict_apply measurableSet_Ico,
    Measure.restrict_restrict measurableSet_Ico,
    inter_eq_left.mpr (interval_subset_unit ha hb)]

lemma intervalLaw_eq_base_withDensity {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) :
    intervalLaw a b = baseLaw.withDensity (fun x =>
      ENNReal.ofReal (uniformDensity baseLaw (Ico a b) x)) := by
  rw [intervalLaw_eq_base_cond ha hb]
  apply cond_eq_withDensity_uniformDensity measurableSet_Ico
  rw [baseLaw_interval_measure ha hb hab.le]
  exact sub_pos.mpr hab

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_OneCoordinateDensity
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace Invariant233.OneCoordinateCoupling

open CouplingMarginalBounds CouplingMixture

lemma intervalDensity_measurable (a b : ℝ) : Measurable (intervalDensity a b) :=
  measurable_const.indicator measurableSet_Ico

lemma intervalDensity_nonneg (a b x : ℝ) : 0 ≤ intervalDensity a b x := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (measureReal_nonneg)]
  · simp [intervalDensity, uniformDensity, hx]

lemma intervalDensity_le_inv_length {a b : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hab : a < b) (x : ℝ) :
    intervalDensity a b x ≤ (b - a)⁻¹ := by
  by_cases hx : x ∈ Ico a b
  · simp [intervalDensity, uniformDensity, hx, baseLaw_interval_measure ha hb hab.le]
  · simp [intervalDensity, uniformDensity, hx, inv_nonneg.mpr (sub_nonneg.mpr hab.le)]

lemma intervalDensity_le_width {a b w : ℝ}
    (ha : 0 ≤ a) (hb : b ≤ 1) (hw : 0 < w) (hlen : w / 2 ≤ b - a) (x : ℝ) :
    intervalDensity a b x ≤ 2 / w := by
  have hab : a < b := by linarith
  apply (intervalDensity_le_inv_length ha hb hab x).trans
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (sub_pos.mpr hab) hw).2
  linarith

lemma leftLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    leftLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (leftDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [leftLaw, leftDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma rightLaw_eq_withDensity {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) :
    rightLaw m a b i = baseLaw.withDensity (fun x => ENNReal.ofReal (rightDensity m a b i x)) := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  fin_cases i <;> simp only [rightLaw, rightDensity] <;>
    apply intervalLaw_eq_base_withDensity <;> linarith

lemma leftDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ leftDensity m a b i x ∧ leftDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [leftDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 0) (b := 1 / m)
        (by norm_num) (by linarith) hinv0 x

lemma rightDensity_bound {m a b : ℝ} (hm : 2 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4)
    (i : Fin 5) (x : ℝ) :
    0 ≤ rightDensity m a b i x ∧ rightDensity m a b i x ≤ componentVarianceBounds m a b i := by
  have hm0 : 0 < m := by linarith
  have hinv0 : 0 < 1 / m := one_div_pos.mpr hm0
  have hinv1 : 1 / m ≤ 1 / 2 := (div_le_iff₀ hm0).2 (by linarith)
  constructor
  · fin_cases i <;> exact intervalDensity_nonneg _ _ _
  · fin_cases i <;> simp only [rightDensity, componentVarianceBounds]
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · apply intervalDensity_le_width <;> linarith
    · simpa using intervalDensity_le_inv_length (a := 1 - 1 / m) (b := 1)
        (by linarith) (by norm_num) (by linarith) x

end Invariant233.OneCoordinateCoupling

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitGeometry
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
namespace Invariant233.CircleDigitCoupling

lemma bin_subset_unit {r : ℕ} [NeZero r] (d : Fin r) :
    bin r d ⊆ Ico (0 : ℝ) 1 := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  intro x hx
  have hd : (d : ℝ) + 1 ≤ r := by exact_mod_cast Nat.succ_le_of_lt d.isLt
  exact ⟨(div_nonneg (by positivity) hr.le).trans hx.1,
    hx.2.trans_le ((div_le_iff₀ hr).mpr (by simpa using hd))⟩

lemma bin_length {r : ℕ} (d : Fin r) :
    ((d : ℝ) + 1) / r - (d : ℝ) / r = 1 / r := by ring

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleDigitCoupling
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

lemma baseLaw_bin {r : ℕ} [NeZero r] (d : Fin r) :
    baseLaw (bin r d) = (r : ℝ≥0∞)⁻¹ := by
  have hr : (0 : ℝ) < r := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne r)
  rw [baseLaw_eq_restrict, Measure.restrict_apply (show MeasurableSet (bin r d) from measurableSet_Ico),
    inter_eq_left.mpr (bin_subset_unit d)]
  rw [bin, Real.volume_Ico, bin_length]
  rw [ENNReal.ofReal_div_of_pos hr]
  simp

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitDensity
attribute [-instance] _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)

include hm ha ha' hb hb' in
lemma endpointLaw_eq_density (side : Bool) (l : Label) :
    endpointLaw side m a b l = baseLaw.withDensity
      (fun x => ENNReal.ofReal (endpointDensity side m a b l x)) := by
  have hm0 : 0 < m := by linarith
  cases l with
  | none => simp [endpointLaw, endpointDensity]
  | some i =>
    cases side
    · exact leftLaw_eq_withDensity (by linarith : 2 ≤ 2 * m)
        (width_pos hm0 ha) ha' (width_pos hm0 hb) hb' i
    · exact rightLaw_eq_withDensity (by linarith : 2 ≤ 2 * m)
        (width_pos hm0 ha) ha' (width_pos hm0 hb) hb' i

lemma endpointDensity_measurable (side : Bool) (m a b : ℝ) (l : Label) :
    Measurable (endpointDensity side m a b l) := by
  cases l with
  | none => exact measurable_const
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_measurable _ _

lemma endpointDensity_nonneg (side : Bool) (m a b : ℝ) (l : Label) (x : ℝ) :
    0 ≤ endpointDensity side m a b l x := by
  cases l with
  | none => norm_num [endpointDensity]
  | some i => cases side <;> fin_cases i <;> exact intervalDensity_nonneg _ _ _

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma marginalDensity_bounds (side : Bool) (x : ℝ) :
    49 / 50 ≤ marginalDensity side κ m a b t x ∧
      marginalDensity side κ m a b t x ≤ 3 + 8 * κ ∧
      marginalDensity side κ m a b t x < 10 := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hd (i : Fin 5) : 0 ≤ endpointDensity side m a b (some i) x ∧
      endpointDensity side m a b (some i) x ≤ componentVarianceBounds (2 * m) a b i := by
    cases side
    · exact leftDensity_bound (by linarith) ha0 ha' hb0 hb' i x
    · exact rightDensity_bound (by linarith) ha0 ha' hb0 hb' i x
  have hρa := rho_div_width_le hκ0 hm0 ha
  have hρb := rho_div_width_le hκ0 hm0 hb
  have hρa0 := rho_nonneg (m := m) (w := a) hκ0
  have hρb0 := rho_nonneg (m := m) (w := b) hκ0
  have hq := diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht
  have htag0 : 0 ≤ t / m := div_nonneg ht0 hm0.le
  have htag : (t / m) * endpointDensity side m a b (some 4) x ≤ 2 := by
    calc
      _ ≤ (t / m) * (2 * m) := mul_le_mul_of_nonneg_left (hd 4).2 htag0
      _ = 2 * t := by field_simp
      _ ≤ 2 := by linarith
  have hw (w : ℝ) (v : ℝ) (hw0 : 0 < w) (hρ : rho κ m w / w ≤ κ)
      (hv : v ≤ 2 / w) : rho κ m w * v ≤ 2 * κ := by
    calc
      _ ≤ rho κ m w * (2 / w) := mul_le_mul_of_nonneg_left hv (rho_nonneg hκ0)
      _ = 2 * (rho κ m w / w) := by ring
      _ ≤ _ := by linarith
  have h0 := hw a _ ha0 hρa (hd 0).2
  have h1 := hw a _ ha0 hρa (hd 1).2
  have h2 := hw b _ hb0 hρb (hd 2).2
  have h3 := hw b _ hb0 hρb (hd 3).2
  have hp0 (i : Fin 5) : 0 ≤ componentProbabilities κ m a b t i *
      endpointDensity side m a b (some i) x :=
    mul_nonneg (componentProbabilities_nonneg hκ0 hm0 ht0 i) (hd i).1
  have hlo : 49 / 50 ≤ marginalDensity side κ m a b t x := by
    exact hq.1.trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => hp0 i)))
  have hup : marginalDensity side κ m a b t x ≤ 3 + 8 * κ := by
    unfold marginalDensity
    simp only [componentProbabilities, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
    change diagonalMass κ m a b t + (rho κ m a * endpointDensity side m a b (some 0) x +
      (rho κ m a * endpointDensity side m a b (some 1) x +
      (rho κ m b * endpointDensity side m a b (some 2) x +
      (rho κ m b * endpointDensity side m a b (some 3) x +
      t / m * endpointDensity side m a b (some 4) x)))) ≤ _
    linarith [hq.2]
  exact ⟨hlo, hup, by linarith⟩

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma ofReal_marginalDensity (side : Bool) (x : ℝ) :
    ENNReal.ofReal (marginalDensity side κ m a b t x) =
      labelMass κ m a b t none + ∑ i : Fin 5,
        labelMass κ m a b t (some i) *
          ENNReal.ofReal (endpointDensity side m a b (some i) x) := by
  have hm0 : 0 < m := by linarith
  apply ofReal_mixture_density
  · exact le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  · exact componentProbabilities_nonneg hκ0 hm0 ht0
  · intro i y
    exact endpointDensity_nonneg side m a b (some i) y

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_eq_integral (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) =
      ∫⁻ x in bin r d, ENNReal.ofReal (marginalDensity side κ m a b t x) ∂baseLaw := by
  have h := withDensity_finite_mixture baseLaw (labelMass κ m a b t none)
    (fun i : Fin 5 => labelMass κ m a b t (some i))
    (fun i x => ENNReal.ofReal (endpointDensity side m a b (some i) x))
    (fun i => (endpointDensity_measurable side m a b (some i)).ennreal_ofReal)
  simp_rw [← ofReal_marginalDensity hκ0 hκ hm ha ha' hb hb' ht0 ht side] at h
  have heval := congrArg (fun ν : Measure ℝ => ν (bin r d)) h
  rw [withDensity_apply _ (show MeasurableSet (bin r d) from measurableSet_Ico)] at heval
  rw [heval, Fintype.sum_option]
  simp only [Measure.add_apply, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [← endpointLaw_eq_density hm ha ha' hb hb' side (some i)]
  rfl

include hκ0 hκ hm ha ha' hb hb' ht0 ht in
lemma digitWeight_total_le_ten (side : Bool) (r : ℕ) (d : Fin r) :
    (∑ l, digitWeight side r κ m a b t l d) ≤ 10 * baseLaw (bin r d) := by
  rw [digitWeight_total_eq_integral hκ0 hκ hm ha ha' hb hb' ht0 ht]
  calc
    _ ≤ ∫⁻ _x in bin r d, (10 : ℝ≥0∞) ∂baseLaw := by
      apply lintegral_mono
      intro x
      exact le_trans (ENNReal.ofReal_le_ofReal
        (marginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht side x).2.2.le)
        (by norm_num)
    _ = _ := by simp

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitDisintegration
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMarginalBounds CouplingMixture OneCoordinateCoupling

private lemma map_label_observe {D : Type*} [MeasurableSpace D]
    (ν : Measure (ℝ × ℝ)) [SFinite ν] (l : Label) (f : ℝ × ℝ → D) (hf : Measurable f) :
    (ν.map (fun z => (l, z))).map (fun z : CoordinateSample => (f z.2, z.1)) =
      (ν.map f).prod (Measure.dirac l) := by
  have hin : Measurable (fun z : ℝ × ℝ => (l, z)) := by fun_prop
  have hout : Measurable (fun z : CoordinateSample => (f z.2, z.1)) := by fun_prop
  rw [Measure.map_map hout hin, Measure.prod_dirac]
  rw [Measure.map_map (show Measurable (fun x : D => (x, l)) from by fun_prop) hf]
  rfl

private lemma observed_pair_left {D : Type*} [MeasurableSpace D]
    (ν η : Measure ℝ) [SFinite ν] [IsProbabilityMeasure η]
    (Q : ℝ → D) (hQ : Measurable Q) :
    (ν.prod η).map (fun z => Q z.1) = ν.map Q := by
  change (ν.prod η).map (Q ∘ Prod.fst) = _
  rw [← Measure.map_map hQ measurable_fst, Measure.map_fst_prod]
  simp

private lemma observed_pair_right {D : Type*} [MeasurableSpace D]
    (ν η : Measure ℝ) [IsProbabilityMeasure ν] [SFinite η]
    (Q : ℝ → D) (hQ : Measurable Q) :
    (ν.prod η).map (fun z => Q z.2) = η.map Q := by
  change (ν.prod η).map (Q ∘ Prod.snd) = _
  rw [← Measure.map_map hQ measurable_snd, Measure.map_snd_prod]
  simp

variable {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
include hm ha ha' hb hb'

lemma endpointLaw_ae_unit (side : Bool) (l : Label) :
    ∀ᵐ x ∂endpointLaw side m a b l, x ∈ Ico (0 : ℝ) 1 := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hinv : 1 / (2 * m) ≤ 1 := by apply (div_le_iff₀ (by linarith : 0 < 2 * m)).2; linarith
  have hinv0 : 0 < 1 / (2 * m) := one_div_pos.mpr (by linarith)
  cases l with
  | none => exact intervalLaw_ae_mem 0 1
  | some i =>
    cases side <;> fin_cases i <;> simp only [endpointLaw, Bool.false_eq_true, ite_false, if_false,
      ite_true, if_true, leftLaw, rightLaw]
    all_goals
      filter_upwards [intervalLaw_ae_mem _ _] with x hx
      constructor <;> linarith [hx.1, hx.2]

lemma endpointLaw_quantize_singleton (side : Bool) (r : ℕ) [NeZero r]
    (l : Label) (d : Fin r) :
    (endpointLaw side m a b l).map (UniformQuantization.quantize r) {d} =
      endpointLaw side m a b l (bin r d) := by
  rw [Measure.map_apply (UniformQuantization.measurable_quantize r) (measurableSet_singleton d)]
  apply measure_congr
  filter_upwards [endpointLaw_ae_unit hm ha ha' hb hb' side l] with x hx
  exact propext (UniformQuantization.quantize_eq_iff d hx)

lemma digitJoint_eq_sum (side : Bool) (r : ℕ) [NeZero r] :
    digitJoint side r κ m a b t =
      ∑ l, labelMass κ m a b t l •
        ((endpointLaw side m a b l).map (UniformQuantization.quantize r)).prod (Measure.dirac l) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have hQ := UniformQuantization.measurable_quantize r
  have hmap : Measurable (fun z : CoordinateSample =>
      (UniformQuantization.quantize r (endpoint side z), z.1)) := by
    cases side <;> dsimp [endpoint] <;> fun_prop
  unfold digitJoint rawLaw labelledMixture
  rw [Measure.map_add _ _ hmap, map_finsetSum _ _ hmap, Fintype.sum_option]
  simp only [Measure.map_smul]
  congr 1
  · cases side <;> simp only [endpoint, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      labelMass, endpointLaw]
    all_goals
      first
      | rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) (by fun_prop)]
      | rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) (by fun_prop)]
      congr 2
      unfold CouplingMixture.diagonal
      have hdiag : Measurable (fun x : ℝ => (x, x)) := by fun_prop
      have hleft : Measurable (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) := by fun_prop
      have hright : Measurable (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) := by fun_prop
      first
      | rw [Measure.map_map hleft hdiag]
      | rw [Measure.map_map hright hdiag]
      rfl
  · apply Finset.sum_congr rfl
    intro i _
    cases side <;> simp only [endpoint, Bool.false_eq_true, ite_false, if_false, ite_true, if_true,
      labelMass, endpointLaw]
    · rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.1) (by fun_prop), observed_pair_left _ _ _ hQ]
    · rw [map_label_observe _ _ (fun z : ℝ × ℝ => UniformQuantization.quantize r z.2) (by fun_prop), observed_pair_right _ _ _ hQ]

lemma digitJoint_fst_singleton (side : Bool) (r : ℕ) [NeZero r] (d : Fin r) :
    (digitJoint side r κ m a b t).fst {d} =
      ∑ l, digitWeight side r κ m a b t l d := by
  rw [digitJoint_eq_sum hm ha ha' hb hb', Measure.fst,
    map_finsetSum _ _ measurable_fst]
  simp only [Measure.map_smul, Measure.map_fst_prod,
    measure_univ, one_smul,
    Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [endpointLaw_quantize_singleton hm ha ha' hb hb']
  rfl

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingLaw
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in
lemma measurable_label (i : ℕ) : Measurable (label i) := by
  exact measurable_fst.comp (measurable_pi_apply i)

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixNonterminal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace Invariant233

theorem infinitePi_eventually_mem_null
    {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    (μ : (n : ℕ) → Measure (X n)) [∀ n, IsProbabilityMeasure (μ n)]
    (s : (n : ℕ) → Set (X n)) (hs : ∀ n, MeasurableSet (s n))
    {q : ℝ≥0∞} (hq : q < 1) (hprob : ∀ n, μ n (s n) ≤ q) :
    (Measure.infinitePi μ) {x | ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ s n} = 0 := by
  have htail (N k : ℕ) :
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} ≤ q ^ k := by
    calc
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} ≤
          (Measure.infinitePi μ) (Set.pi (Finset.Ico N (N + k)) s) := by
        apply measure_mono
        intro x hx n hn
        exact hx n (Finset.mem_Ico.mp hn).1
      _ = ∏ n ∈ Finset.Ico N (N + k), μ n (s n) :=
        Measure.infinitePi_pi μ (fun n _ => hs n)
      _ ≤ ∏ _n ∈ Finset.Ico N (N + k), q :=
        Finset.prod_le_prod' (fun n _ => hprob n)
      _ = q ^ k := by simp
  have hnull (N : ℕ) :
      (Measure.infinitePi μ) {x | ∀ n, N ≤ n → x n ∈ s n} = 0 := by
    apply le_antisymm _ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq)
      (Eventually.of_forall (htail N))
  have heq : {x : (n : ℕ) → X n | ∃ N : ℕ, ∀ n, N ≤ n → x n ∈ s n} =
      ⋃ N : ℕ, {x | ∀ n, N ≤ n → x n ∈ s n} := by
    ext x
    simp
  rw [heq]
  exact measure_iUnion_null hnull

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingNonterminal
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

lemma initial_digit_singleton {p : CircleParameterData}
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ)
    (d : Fin (MixedRadix.radices p.q i)) :
    (initialLaw.map (observedDigit p hr side i)) {d} =
      (MixedRadix.radices p.q i : ℝ≥0∞)⁻¹ := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  rw [initialLaw, Measure.map_map (measurable_observedDigit hr side i)
    (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop)]
  cases side <;>
    change (baseLaw.map (UniformQuantization.quantize _)) {d} = _
  all_goals rw [baseLaw_eq_restrict]; exact UniformQuantization.map_quantize_singleton _ d

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma observed_singleton_le_half (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) (i : ℕ)
    (d : Fin (MixedRadix.radices p.q i)) :
    ((coordinateLaw p j i).map (observedDigit p hr side i)) {d} ≤ (2 : ℝ≥0∞)⁻¹ := by
  let : NeZero (MixedRadix.radices p.q i) := ⟨Nat.ne_of_gt (hr i)⟩
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initial_digit_singleton]
    exact ENNReal.inv_le_inv.mpr (by exact_mod_cast
      (MixedRadix.radices_ge_two hp.q_pos hp.frequency_increasing hp.frequency_divisible i))
  obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (by omega)
  have hidx := p.blockIndex_eq_of_mem hp.m_pos his
  have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast (show 100 ≤ p.m s by have := hp.m_ge_200 s hs; omega)
  have ha := hp.coupling_a_bounds s hs
  have hb := hp.coupling_b_bounds s hs
  have hκ := CircleParameterLaws.coupling_kappa_bounds s hs
  have ht := tag_bounds j s
  have h20 : (20 : ℝ) ≤ MixedRadix.radices p.q i := by
    have hN := hp.coupling_radix_ge_N hs his
    have hK : (100 : ℝ) ≤ p.K s := by exact_mod_cast hp.coupling_K_ge s hs
    dsimp [N] at hN
    nlinarith
  rw [coordinateLaw, ite_eq_right hi, hidx]
  have hfst := Measure.fst_map_prodMk (μ := rawLaw (kappa s) (p.m s) (p.a s) (p.b s) (tag j s))
    (X := observedDigit p hr side i) measurable_fst
  rw [← hfst]
  change (digitJoint side (MixedRadix.radices p.q i) (kappa s) (p.m s) (p.a s) (p.b s) (tag j s)).fst {d} ≤ _
  rw [digitJoint_fst_singleton hm ha.1 ha.2 hb.1 hb.2]
  calc
    _ ≤ 10 * baseLaw (bin _ d) := digitWeight_total_le_ten hκ.1 hκ.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side _ d
    _ = 10 * (MixedRadix.radices p.q i : ℝ≥0∞)⁻¹ := by rw [baseLaw_bin]
    _ ≤ 10 * (20 : ℝ≥0∞)⁻¹ := mul_le_mul_right (ENNReal.inv_le_inv.mpr (by exact_mod_cast h20)) 10
    _ = _ := by
      apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
      norm_num

lemma ae_nonterminal_digits (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (side : Bool) :
    ∀ᵐ ω ∂law p j, MixedRadix.Nonterminal (digits p hr side ω) := by
  let := coordinateLaw_isProbabilityMeasure hp j
  let s : ℕ → Set CoordinateSample := fun i =>
    {z | ¬(observedDigit p hr side i z : ℕ) + 1 < MixedRadix.radices p.q i}
  have heq (i : ℕ) : s i = observedDigit p hr side i ⁻¹'
      {⟨MixedRadix.radices p.q i - 1, by have := hr i; omega⟩} := by
    ext z
    simp only [s, mem_ofPred_eq, mem_preimage, mem_singleton_iff, Fin.ext_iff]
    have := (observedDigit p hr side i z).isLt
    omega
  have hs (i : ℕ) : MeasurableSet (s i) := by
    rw [heq]
    exact (measurable_observedDigit hr side i) (measurableSet_singleton _)
  have hprob (i : ℕ) : coordinateLaw p j i (s i) ≤ (2 : ℝ≥0∞)⁻¹ := by
    rw [heq, ← Measure.map_apply (measurable_observedDigit hr side i) (measurableSet_singleton _)]
    exact observed_singleton_le_half hp j hr side i _
  have hnull := infinitePi_eventually_mem_null (coordinateLaw p j) s hs
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1) hprob
  rw [ae_iff]
  simpa only [law, MixedRadix.Nonterminal, digits, mem_ofPred_eq,
    not_forall, not_exists, not_and, s] using hnull

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingSupport
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators
namespace Invariant233.CircleDigitCoupling
open CouplingMixture CouplingMarginalBounds OneCoordinateCoupling

lemma rawLaw_ae_of_components {κ m a b t : ℝ} {P : CoordinateSample → Prop}
    (hP : MeasurableSet {z | P z})
    (hdiag : ∀ᵐ x ∂baseLaw, P (none, (x, x)))
    (hcomp : ∀ i : Fin 5, ∀ᵐ z ∂(leftLaw (2 * m) a b i).prod (rightLaw (2 * m) a b i),
      P (some i, z)) : ∀ᵐ z ∂rawLaw κ m a b t, P z := by
  unfold rawLaw labelledMixture
  rw [ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (show Measurable (fun z : ℝ × ℝ => ((none : Label), z)) from by fun_prop).aemeasurable hP).2
    unfold CouplingMixture.diagonal
    exact (ae_map_iff (show Measurable (fun x : ℝ => (x, x)) from by fun_prop).aemeasurable
      (show MeasurableSet {z : ℝ × ℝ | P (none, z)} from
        (show Measurable (fun z : ℝ × ℝ => ((none : Label), z)) from by fun_prop) hP)).2 hdiag
  · intro i _
    exact Measure.ae_smul_measure
      ((ae_map_iff (show Measurable (fun z : ℝ × ℝ => (some i, z)) from by fun_prop).aemeasurable hP).2 (hcomp i)) _

section Parameters
variable {κ m a b t : ℝ}
    (hm : 100 ≤ m) (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
include hm ha ha' hb hb'

lemma rawLaw_ae_endpoint_property (side : Bool) {P : Label → ℝ → Prop}
    (hP : MeasurableSet {z : CoordinateSample | P z.1 (endpoint side z)})
    (hbase : ∀ᵐ x ∂baseLaw, P none x)
    (hl : ∀ i : Fin 5, ∀ᵐ x ∂endpointLaw side m a b (some i), P (some i) x) :
    ∀ᵐ z ∂rawLaw κ m a b t, P z.1 (endpoint side z) := by
  have hm0 : 0 < m := by linarith
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) (width_pos hm0 ha) ha' (width_pos hm0 hb) hb'
  apply rawLaw_ae_of_components hP
  · cases side <;> exact hbase
  · intro i
    cases side
    · exact (measurePreserving_fst (μ := leftLaw (2 * m) a b i)
        (ν := rightLaw (2 * m) a b i)).quasiMeasurePreserving.ae (hl i)
    · exact (measurePreserving_snd (μ := leftLaw (2 * m) a b i)
        (ν := rightLaw (2 * m) a b i)).quasiMeasurePreserving.ae (hl i)

lemma rawLaw_ae_endpoint_unit (side : Bool) :
    ∀ᵐ z ∂rawLaw κ m a b t, endpoint side z ∈ Ico (0 : ℝ) 1 := by
  apply rawLaw_ae_endpoint_property hm ha ha' hb hb' side (P := fun _ x => x ∈ Ico (0 : ℝ) 1)
  · apply measurableSet_Ico.preimage
    cases side
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  · exact intervalLaw_ae_mem 0 1
  · intro i
    exact endpointLaw_ae_unit hm ha ha' hb hb' side (some i)

end Parameters
end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingForcing
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal
namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

lemma ae_endpoint_unit (j : ℕ) (i : ℕ) (side : Bool) :
    ∀ᵐ ω ∂law p j, endpoint side (ω i) ∈ Ico (0 : ℝ) 1 := by
  let := coordinateLaw_isProbabilityMeasure hp j
  apply (measurePreserving_eval_infinitePi (coordinateLaw p j) i).quasiMeasurePreserving.ae
    (p := fun z => endpoint side z ∈ Ico (0 : ℝ) 1)
  by_cases hi : i = 0
  · rw [coordinateLaw, ite_eq_left hi, initialLaw]
    apply (ae_map_iff (show Measurable (fun x : ℝ => ((none : Label), (x, x))) from by fun_prop).aemeasurable
      (show MeasurableSet {z : CoordinateSample | endpoint side z ∈ Ico (0 : ℝ) 1} from by
        apply measurableSet_Ico.preimage
        cases side
        · exact measurable_fst.comp measurable_snd
        · exact measurable_snd.comp measurable_snd)).2
    cases side <;> exact CouplingMixture.intervalLaw_ae_mem 0 1
  · have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
    have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by exact_mod_cast
      (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
    rw [coordinateLaw, ite_eq_right hi]
    exact rawLaw_ae_endpoint_unit hm (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
      (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2 side

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleCouplingAttenuation
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData CouplingMarginalBounds
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

omit hp in
lemma measurableSet_tagEvent (p : CircleParameterData) (j : ℕ) :
    MeasurableSet (tagEvent p j) := by
  simp only [tagEvent, Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro i
  by_cases hi : i ∈ p.block j
  · simpa only [hi, true_and] using
      (measurableSet_eq_fun (measurable_label i) (measurable_const (a := (some 4 : Label))))
  · simp only [hi, false_and, Set.ofPred_false, MeasurableSet.empty]

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleTruncationEvent
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleCoupling

lemma truncationEvent_subset_tagEvent (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) :
    truncationEvent p j hr r ⊆ tagEvent p j := fun _ h => h.2.1

lemma measurableSet_truncationEvent {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ} (hrm : Measurable r) :
    MeasurableSet (truncationEvent p j hr r) := by
  have hx (i : ℕ) : Measurable (fun ω : Sample => (ω i).2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_pi_apply i))
  have hy (i : ℕ) : Measurable (fun ω : Sample => (ω i).2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_pi_apply i))
  simp only [truncationEvent, Set.ofPred_and, Set.ofPred_forall]
  refine MeasurableSet.inter ?_ ((measurableSet_tagEvent p j).inter
    (MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)))
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      (measurableSet_lt (hx i) measurable_const).inter
        (measurableSet_lt measurable_const (hy i))
  · exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        (measurableSet_lt (hx i) measurable_const).inter
          (measurableSet_lt measurable_const (hy i))
  · exact measurableSet_le measurable_const (hrm.comp (measurable_point hp hr false))
  · exact measurableSet_le measurable_const
      (measurable_const.sub (hrm.comp (measurable_point hp hr true)))

end Invariant233.CircleCoupling

end

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

@[simp] theorem cocycleVersion_zero {I : Type*} (θ c : I → ℝ) (x : Space I) :
    cocycleVersion θ c 0 x = 1 := by
  simp only [cocycleVersion, Int.cast_zero, zero_mul, add_zero]
  exact FiniteSupportCocycle.exp_tsum_floor_zero _ c
    (fun i ↦ representative_mem_Ico (x i))

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CocycleWindowBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Set

open scoped BigOperators ComplexConjugate lp
namespace Invariant233.CocycleWindowBounds

theorem floor_forward_eq_zero {x α v K : ℝ}
    (hx : 0 ≤ x) (hα : 0 ≤ α) (hv : 0 ≤ v) (hvK : v ≤ K)
    (hexclude : x + K * α < 1) : ⌊x + v * α⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · positivity
  · have hmul := mul_le_mul_of_nonneg_right hvK hα
    linarith

theorem floor_backward_eq_zero {y α v K : ℝ}
    (hy : y < 1) (hα : 0 ≤ α) (hv : 0 ≤ v) (hvK : v ≤ K)
    (hexclude : K * α ≤ y) : ⌊y - v * α⌋ = 0 := by
  apply Int.floor_eq_zero_iff.mpr
  constructor
  · exact sub_nonneg.mpr ((mul_le_mul_of_nonneg_right hvK hα).trans hexclude)
  · exact (sub_le_self y (mul_nonneg hv hα)).trans_lt hy

theorem floor_forward_le {x α v : ℝ} (K : ℕ)
    (hx : x < 1) (hα : α ≤ 1) (hv : 0 ≤ v) (hvK : v ≤ K) :
    (⌊x + v * α⌋ : ℝ) ≤ (K : ℝ) + 1 := by
  have hmul : v * α ≤ (K : ℝ) :=
    (mul_le_mul_of_nonneg_left hα hv).trans (by simpa using hvK)
  linarith [Int.floor_le (x + v * α)]

theorem neg_floor_backward_le {y α v : ℝ} (K : ℕ)
    (hy : 0 ≤ y) (hα : α ≤ 1) (hv : 0 ≤ v) (hvK : v ≤ K) :
    -(⌊y - v * α⌋ : ℝ) ≤ (K : ℝ) + 1 := by
  have hmul : v * α ≤ (K : ℝ) :=
    (mul_le_mul_of_nonneg_left hα hv).trans (by simpa using hvK)
  linarith [Int.lt_floor_add_one (y - v * α)]

theorem tsum_weighted_le_prefix {I : Type*} (s : Finset I)
    (c a : I → ℝ) (B : ℝ) (hc : ∀ i, 0 ≤ c i)
    (hout : ∀ i ∉ s, a i = 0) (hbound : ∀ i ∈ s, a i ≤ B) :
    (∑' i, c i * a i) ≤ B * ∑ i ∈ s, c i := by
  rw [tsum_eq_sum (s := s) (fun i hi => by rw [hout i hi]; simp)]
  calc
    (∑ i ∈ s, c i * a i) ≤ ∑ i ∈ s, c i * B :=
      Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hbound i hi) (hc i))
    _ = B * ∑ i ∈ s, c i := by rw [← Finset.sum_mul]; ring

theorem signed_floor_sums_le {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    (∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ)) ≤
        ((K : ℝ) + 1) * ∑ i ∈ s, c i ∧
    -(∑' i, c i * (⌊y i - (v : ℝ) * α i⌋ : ℝ)) ≤
        ((K : ℝ) + 1) * ∑ i ∈ s, c i := by
  have hcost : 0 ≤ ((K : ℝ) + 1) * ∑ i ∈ s, c i := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => hc i)
  rcases le_or_gt 0 v with hv0 | hv0
  · have hv0' : (0 : ℝ) ≤ v := by exact_mod_cast hv0
    have hvK : (v : ℝ) ≤ K := by exact_mod_cast (le_abs_self v).trans hv
    constructor
    · apply tsum_weighted_le_prefix s c _ _ hc
      · intro i hi
        rw [floor_forward_eq_zero (hx i).1 (hα i).1 hv0' hvK (hleft i hi)]
        simp
      · intro i _
        exact floor_forward_le K (hx i).2 (hα i).2 hv0' hvK
    · rw [← tsum_neg]
      have heq : (fun i => -(c i * (⌊y i - (v : ℝ) * α i⌋ : ℝ))) =
          (fun i => c i * -(⌊y i - (v : ℝ) * α i⌋ : ℝ)) := by
        funext i; ring
      rw [heq]
      apply tsum_weighted_le_prefix s c _ _ hc
      · intro i hi
        rw [floor_backward_eq_zero (hy i).2 (hα i).1 hv0' hvK (hright i hi)]
        simp
      · intro i _
        exact neg_floor_backward_le K (hy i).1 (hα i).2 hv0' hvK
  · have hv0' : (v : ℝ) ≤ 0 := by exact_mod_cast hv0.le
    constructor
    · apply le_trans (tsum_nonpos fun i => ?_) hcost
      apply mul_nonpos_of_nonneg_of_nonpos (hc i)
      have hf : ⌊x i + (v : ℝ) * α i⌋ ≤ 0 := by
        apply Int.floor_le_iff.mpr
        norm_num
        exact (add_le_of_nonpos_right (mul_nonpos_of_nonpos_of_nonneg hv0' (hα i).1)).trans_lt
          (hx i).2
      exact_mod_cast hf
    · apply le_trans (neg_nonpos.mpr (tsum_nonneg fun i => ?_)) hcost
      apply mul_nonneg (hc i)
      have hf : (0 : ℤ) ≤ ⌊y i - (v : ℝ) * α i⌋ := by
        apply Int.floor_nonneg.mpr
        exact sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hv0' (hα i).1).trans (hy i).1)
      exact_mod_cast hf

theorem cocycle_bounds {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    1 / Real.exp (-(∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ))) ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
    Real.exp (-(∑' i, c i * (⌊y i + ((-v : ℤ) : ℝ) * α i⌋ : ℝ))) ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  obtain ⟨hforward, hbackward⟩ :=
    signed_floor_sums_le s x y α c K hx hy hα hc hleft hright v hv
  constructor
  · simpa only [Real.exp_neg, one_div, inv_inv] using Real.exp_le_exp.mpr hforward
  · simpa only [Int.cast_neg, neg_mul, sub_eq_add_neg] using
      Real.exp_le_exp.mpr hbackward

theorem coefficient_bounds {I : Type*} (s : Finset I)
    (x y α c : I → ℝ) (K : ℕ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, x i + (K : ℝ) * α i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * α i ≤ y i)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1)
    (v : ℤ) (hv : |v| ≤ (K : ℤ)) :
    ‖ξ v / (Real.exp (-(∑' i, c i * (⌊x i + (v : ℝ) * α i⌋ : ℝ))) : ℂ)‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) ∧
    ‖(Real.exp (-(∑' i, c i * (⌊y i + ((-v : ℤ) : ℝ) * α i⌋ : ℝ))) : ℂ) *
        conj (γ (-v))‖ ≤ Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i) := by
  obtain ⟨hforward, hbackward⟩ :=
    cocycle_bounds s x y α c K hx hy hα hc hleft hright v hv
  have hξv : ‖ξ v‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) ξ v).trans hξ
  have hγv : ‖γ (-v)‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) γ (-v)).trans hγ
  constructor
  · simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (div_le_div_of_nonneg_right hξv (Real.exp_pos _).le).trans hforward
  · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), Complex.norm_conj]
    exact (mul_le_of_le_one_right (Real.exp_pos _).le hγv).trans hbackward

end Invariant233.CocycleWindowBounds

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycleWindow
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp
namespace Invariant233.ProductCocycle

theorem finite_window_coefficients {I : Type*} (s : Finset I)
    (θ c : I → ℝ) (K : ℕ) (x y : Space I)
    (hθ : ∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) (hc : ∀ i, 0 ≤ c i)
    (hleft : ∀ i ∉ s, representative (x i) + (K : ℝ) * θ i < 1)
    (hright : ∀ i ∉ s, (K : ℝ) * θ i ≤ representative (y i))
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (K : ℤ) →
      ‖ξ v / (cocycleVersion θ c v x : ℂ)‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i)) ∧
    (∀ v : ℤ, |v| ≤ (K : ℤ) →
      ‖(cocycleVersion θ c (-v) y : ℂ) * conj (γ (-v))‖ ≤
        Real.exp (((K : ℝ) + 1) * ∑ i ∈ s, c i)) := by
  have h := fun v hv => CocycleWindowBounds.coefficient_bounds s
    (fun i => representative (x i)) (fun i => representative (y i)) θ c K
    (fun i => representative_mem_Ico (x i)) (fun i => representative_mem_Ico (y i))
    hθ hc hleft hright ξ γ hξ hγ v hv
  exact ⟨fun v hv => (h v hv).1, fun v hv => (h v hv).2⟩

end Invariant233.ProductCocycle

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleCocycleWindow
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.CircleParameterData

theorem sum_flattenedCost_prefix (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (j : ℕ) :
    (∑ n ∈ Finset.range (p.blockEnd j), p.flattenedCost n) =
      ∑ s ∈ Finset.Icc 1 j, p.C s * (p.m s : ℝ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [p.blockEnd_succ, Finset.sum_range_add, ih,
      Finset.sum_Icc_succ_top (by omega)]
    congr 1
    calc
      (∑ n ∈ Finset.range (p.m (j + 1)), p.flattenedCost (p.blockEnd j + n)) =
          ∑ _n ∈ Finset.range (p.m (j + 1)), p.C (j + 1) := by
        apply Finset.sum_congr rfl
        intro n hn
        apply p.flattenedCost_eq_of_mem hm
        rw [p.mem_block_iff, Nat.add_sub_cancel, p.blockEnd_succ]
        have hn' := Finset.mem_range.mp hn
        constructor <;> omega
      _ = p.C (j + 1) * (p.m (j + 1) : ℝ) := by simp [nsmul_eq_mul, mul_comm]

theorem exists_late_block (p : CircleParameterData)
    (hm : ∀ j, 1 ≤ j → 0 < p.m j) (j n : ℕ) (hj : 1 ≤ j)
    (hn : n ∉ Finset.range (p.blockEnd (j - 1))) :
    ∃ s, j ≤ s ∧ n + 1 ∈ p.block s := by
  obtain ⟨s, hs, hmem⟩ := p.exists_mem_block hm (n + 1) (by omega)
  refine ⟨s, ?_, hmem⟩
  have hn' : p.blockEnd (j - 1) ≤ n := by simpa using hn
  have hi := ((p.mem_block_iff s (n + 1)).mp hmem).2
  by_contra h
  have hsj : s ≤ j - 1 := by omega
  have hd := (p.blockEnd_strictMono hm).monotone hsj
  omega

theorem coordinate_circleValue (p : CircleParameterData)
    (d : MixedRadix.Digits (MixedRadix.radices p.q)) (i : ℕ) :
    p.coordinate i (MixedRadix.circleValue d) =
      Int.fract ((p.q i : ℝ) * MixedRadix.ofDigits d) := by
  unfold coordinate rep MixedRadix.circleValue
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  exact CircleCharacterDynamics.representative_coe _

end Invariant233.CircleParameterData

namespace Invariant233.CocycleWindowBounds

theorem exclusions_of_rounding {x y X Y K N : ℝ}
    (hK : 1 ≤ K) (hN : 0 < N)
    (hx : |x - X| ≤ 1 / N) (hy : |y - Y| ≤ 1 / N)
    (hX : X < 1 - 3 * K / N) (hY : 3 * K / N < Y) :
    x < 1 - 2 * K / N ∧ 2 * K / N < y := by
  have hdiv : 1 / N ≤ K / N := div_le_div_of_nonneg_right hK hN.le
  have hxx := (abs_le.mp hx).2
  have hyy := (abs_le.mp hy).1
  simp only [mul_div_assoc] at hX hY ⊢
  constructor <;> linarith

end Invariant233.CocycleWindowBounds

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem coordinate_raw_error_le (s : ℕ) (hs : 1 ≤ s) (i : ℕ) (hi : i ∈ p.block s)
    (d : MixedRadix.Digits (MixedRadix.radices p.q)) (hd : MixedRadix.Nonterminal d)
    (X : ℝ) (hX : 0 ≤ X)
    (hfloor : ⌊(MixedRadix.radices p.q i : ℝ) * X⌋₊ = (d i : ℕ)) :
    |p.coordinate i (MixedRadix.circleValue d) - X| ≤ 1 / p.N s := by
  rw [p.coordinate_circleValue]
  apply (MixedRadix.abs_coordinate_sub_raw_le hp.frequency_zero hp.q_pos
    hp.frequency_increasing hp.frequency_divisible d hd i hX hfloor).trans
  have hN : 0 < p.N s := by
    unfold CircleParameterData.N
    exact mul_pos (by exact_mod_cast hp.m_pos s hs) (by exact_mod_cast hp.K_pos s hs)
  apply one_div_le_one_div_of_le hN
  simpa only [MixedRadix.radices, Nat.cast_div_charZero (hp.frequency_divisible i)] using
    hp.frequency_ratios s hs i hi

theorem raw_good_event_exclusions (j : ℕ) (hj : 1 ≤ j)
    (d e : MixedRadix.Digits (MixedRadix.radices p.q))
    (hd : MixedRadix.Nonterminal d) (he : MixedRadix.Nonterminal e)
    (X Y : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hdigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * X i⌋₊ = (d i : ℕ))
    (hedigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * Y i⌋₊ = (e i : ℕ))
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      X i < 1 - 3 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      3 * (p.K j : ℝ) / p.N s < Y i) :
    ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i (MixedRadix.circleValue d) < 1 - 2 * (p.K j : ℝ) / p.N s ∧
        2 * (p.K j : ℝ) / p.N s < p.coordinate i (MixedRadix.circleValue e) := by
  intro s hsj i hi
  have hs : 1 ≤ s := hj.trans hsj
  have hN : 0 < p.N s := by
    unfold CircleParameterData.N
    exact mul_pos (by exact_mod_cast hp.m_pos s hs) (by exact_mod_cast hp.K_pos s hs)
  exact CocycleWindowBounds.exclusions_of_rounding
    (by exact_mod_cast hp.K_pos j hj) hN
    (hp.coordinate_raw_error_le s hs i hi d hd (X i) (hX i) (hdigit i))
    (hp.coordinate_raw_error_le s hs i hi e he (Y i) (hY i) (hedigit i))
    (hleft s hsj i hi) (hright s hsj i hi)

theorem current_margin_eq (j : ℕ) (hj : 1 ≤ j) (a : ℝ) :
    a * (p.K j : ℝ) / p.N j = a / (p.m j : ℝ) := by
  have hK : (p.K j : ℝ) ≠ 0 := by exact_mod_cast (hp.K_pos j hj).ne'
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j hj).ne'
  unfold CircleParameterData.N
  field_simp

theorem source_good_event_exclusions (j : ℕ) (hj : 1 ≤ j)
    (d e : MixedRadix.Digits (MixedRadix.radices p.q))
    (hd : MixedRadix.Nonterminal d) (he : MixedRadix.Nonterminal e)
    (X Y : ℕ → ℝ) (hX : ∀ i, 0 ≤ X i) (hY : ∀ i, 0 ≤ Y i)
    (hdigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * X i⌋₊ = (d i : ℕ))
    (hedigit : ∀ i, ⌊(MixedRadix.radices p.q i : ℝ) * Y i⌋₊ = (e i : ℕ))
    (hcurrent : ∀ i ∈ p.block j,
      X i < 1 - 3 / (p.m j : ℝ) ∧ 3 / (p.m j : ℝ) < Y i)
    (hfuture : ∀ s, j < s → ∀ i ∈ p.block s,
      X i < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < Y i) :
    ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i (MixedRadix.circleValue d) < 1 - 2 * (p.K j : ℝ) / p.N s ∧
        2 * (p.K j : ℝ) / p.N s < p.coordinate i (MixedRadix.circleValue e) := by
  have hraw : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      X i < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < Y i := by
    intro s hsj i hi
    rcases eq_or_lt_of_le hsj with h | h
    · subst s
      simpa only [hp.current_margin_eq j hj 3] using hcurrent i hi
    · exact hfuture s h i hi
  exact hp.raw_good_event_exclusions j hj d e hd he X Y hX hY hdigit hedigit
    (fun s hs i hi => (hraw s hs i hi).1) (fun s hs i hi => (hraw s hs i hi).2)

theorem finite_window_coefficients (j : ℕ) (hj : 1 ≤ j) (x y : Circle)
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < p.coordinate i y)
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖ξ v / (ProductCocycle.cocycleVersion
        (fun n => p.alpha θ (n + 1)) p.flattenedCost v
        (fun n => p.q (n + 1) • x) : ℂ)‖ ≤ p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(ProductCocycle.cocycleVersion
        (fun n => p.alpha θ (n + 1)) p.flattenedCost (-v)
        (fun n => p.q (n + 1) • y) : ℂ) * conj (γ (-v))‖ ≤ p.coefficientBound j) := by
  have hc (n : ℕ) : 0 ≤ p.flattenedCost n :=
    (hp.C_pos _ (p.blockIndex_pos hp.m_pos (by omega))).le
  have hα (n : ℕ) : p.alpha θ (n + 1) ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hexclude (n : ℕ) (hn : n ∉ Finset.range (p.blockEnd (j - 1))) :
      p.coordinate (n + 1) x + (p.K j : ℝ) * p.alpha θ (n + 1) < 1 ∧
        (p.K j : ℝ) * p.alpha θ (n + 1) ≤ p.coordinate (n + 1) y := by
    obtain ⟨s, hsj, hns⟩ := p.exists_late_block hp.m_pos j n hj hn
    have hs : 1 ≤ s := hj.trans hsj
    have hphase := (hp.phase_bounds s hs (n + 1) hns).2
    have hmul := mul_le_mul_of_nonneg_left hphase.le (Nat.cast_nonneg (p.K j))
    have hbound : (p.K j : ℝ) * p.alpha θ (n + 1) ≤ 2 * (p.K j : ℝ) / p.N s := by
      calc
        _ ≤ (p.K j : ℝ) * (2 / p.N s) := hmul
        _ = _ := by ring
    constructor
    · linarith [hleft s hsj (n + 1) hns]
    · exact hbound.trans (hright s hsj (n + 1) hns).le
  have h := ProductCocycle.finite_window_coefficients
    (Finset.range (p.blockEnd (j - 1))) (fun n => p.alpha θ (n + 1)) p.flattenedCost
    (p.K j) (fun n => p.q (n + 1) • x) (fun n => p.q (n + 1) • y) hα hc
    (fun n hn => (hexclude n hn).1) (fun n hn => (hexclude n hn).2) ξ γ hξ hγ
  simpa only [p.sum_flattenedCost_prefix hp.m_pos, CircleParameterData.coefficientBound] using h

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CanonicalCircleCoefficients
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem parameter_cocycle_eq_product (k : ℤ) (x : Circle) :
    p.floorCocycle θ k x = ProductCocycle.cocycleVersion
      (fun n => p.alpha θ (n + 1)) p.flattenedCost k
      (fun n => p.q (n + 1) • x) := by
  rw [hp.parameter_cocycle_eq_flattened]
  simp only [CircleWeights.cocycle, CircleWeights.floorCost,
    ProductCocycle.cocycleVersion, CircleWeights.coordinate,
    CircleWeights.representative, CircleWeights.phase,
    CircleParameterData.flattenedFrequency, CircleParameterData.alpha,
    ProductCocycle.representative, Int.cast_natCast, natCast_zsmul]

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ProjectionCocycleWindow
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped lp ComplexConjugate InnerProductSpace

namespace Invariant233.ProjectionCocycleWindow

theorem projection_vector_norm_le (P : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) : ‖P basisZero‖ ≤ 1 := by
  calc
    ‖P basisZero‖ ≤ ‖P‖ * ‖basisZero‖ := P.le_opNorm basisZero
    _ = ‖P‖ := by simp
    _ ≤ 1 := IsStarProjection.norm_le P hP

theorem complement_vector_norm_le (Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hQ : IsStarProjection Q) : ‖(1 - Q) basisZero‖ ≤ 1 :=
  projection_vector_norm_le (1 - Q) hQ.one_sub

theorem central_lower_bounds (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (a : ℝ) (hP : a ≤ ((P basisZero) 0).re)
    (hQ : ((Q basisZero) 0).re ≤ 1 - a) :
    a ≤ ‖(P basisZero) 0‖ ∧ a ≤ ‖conj (((1 - Q) basisZero) 0)‖ := by
  constructor
  · exact hP.trans (Complex.re_le_norm _)
  · rw [Complex.norm_conj]
    apply le_trans _ (Complex.re_le_norm _)
    have hcoord : ((1 - Q) basisZero) 0 = 1 - (Q basisZero) 0 := by
      simp only [sub_apply, one_apply_eq_self, lp.coeFn_sub, Pi.sub_apply, basisZero_zero]
    rw [hcoord, Complex.sub_re, Complex.one_re]
    linarith

theorem circle_coefficient_properties {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) (hj : 1 ≤ j) (x y : Circle)
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < p.coordinate i y)
    (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (a : ℝ) (hPdiag : a ≤ ((P basisZero) 0).re)
    (hQdiag : ((Q basisZero) 0).re ≤ 1 - a) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(P basisZero) v / (ProductCocycle.cocycleVersion
        (fun n => p.alpha θ (n + 1)) p.flattenedCost v
        (fun n => p.q (n + 1) • x) : ℂ)‖ ≤ p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(ProductCocycle.cocycleVersion
        (fun n => p.alpha θ (n + 1)) p.flattenedCost (-v)
        (fun n => p.q (n + 1) • y) : ℂ) *
        conj (((1 - Q) basisZero) (-v))‖ ≤ p.coefficientBound j) ∧
    a ≤ ‖(P basisZero) 0 / (ProductCocycle.cocycleVersion
      (fun n => p.alpha θ (n + 1)) p.flattenedCost 0
      (fun n => p.q (n + 1) • x) : ℂ)‖ ∧
    a ≤ ‖(ProductCocycle.cocycleVersion
      (fun n => p.alpha θ (n + 1)) p.flattenedCost 0
      (fun n => p.q (n + 1) • y) : ℂ) * conj (((1 - Q) basisZero) 0)‖ := by
  obtain ⟨hA, hB⟩ := hp.finite_window_coefficients j hj x y hleft hright
    (P basisZero) ((1 - Q) basisZero)
    (projection_vector_norm_le P hP) (complement_vector_norm_le Q hQ)
  obtain ⟨hA0, hB0⟩ := central_lower_bounds P Q a hPdiag hQdiag
  exact ⟨hA, hB, by simpa using hA0, by simpa using hB0⟩

end Invariant233.ProjectionCocycleWindow

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CanonicalCircleFiniteLower
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem canonical_projection_coefficient_properties (j : ℕ) (hj : 1 ≤ j)
    (x y : Circle)
    (hleft : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * (p.K j : ℝ) / p.N s)
    (hright : ∀ s, j ≤ s → ∀ i ∈ p.block s,
      2 * (p.K j : ℝ) / p.N s < p.coordinate i y)
    (P Q : ℓ²(ℤ, ℂ) →L[ℂ] ℓ²(ℤ, ℂ))
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (a : ℝ) (hPdiag : a ≤ ((P ProjectionCocycleWindow.basisZero) 0).re)
    (hQdiag : ((Q ProjectionCocycleWindow.basisZero) 0).re ≤ 1 - a) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(P ProjectionCocycleWindow.basisZero) v / (p.floorCocycle θ v x : ℂ)‖ ≤
        p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(p.floorCocycle θ (-v) y : ℂ) *
        conj (((1 - Q) ProjectionCocycleWindow.basisZero) (-v))‖ ≤
        p.coefficientBound j) ∧
    a ≤ ‖(P ProjectionCocycleWindow.basisZero) 0 / (p.floorCocycle θ 0 x : ℂ)‖ ∧
    a ≤ ‖(p.floorCocycle θ 0 y : ℂ) *
      conj (((1 - Q) ProjectionCocycleWindow.basisZero) 0)‖ := by
  simpa only [hp.parameter_cocycle_eq_product] using
    ProjectionCocycleWindow.circle_coefficient_properties hp j hj x y hleft hright
      P Q hP hQ a hPdiag hQdiag

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleTruncationIntegral
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem ae_truncationEvent_exclusions (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) :
    ∀ᵐ ω ∂law p j, ω ∈ truncationEvent p j hr r →
      ∀ s, j ≤ s → ∀ i ∈ p.block s,
        p.coordinate i (point p hr false ω) < 1 - 2 * (p.K j : ℝ) / p.N s ∧
        2 * (p.K j : ℝ) / p.N s < p.coordinate i (point p hr true ω) := by
  have hu (side : Bool) : ∀ᵐ ω ∂law p j, ∀ i,
      endpoint side (ω i) ∈ Ico (0 : ℝ) 1 :=
    ae_all_iff.mpr (fun i => ae_endpoint_unit hp j i side)
  filter_upwards [hu false, hu true, ae_nonterminal_digits hp j hr false,
    ae_nonterminal_digits hp j hr true] with ω hx hy hdx hdy
  intro hE
  have hfloor (side : Bool) (hunit : ∀ i, endpoint side (ω i) ∈ Ico (0 : ℝ) 1)
      (i : ℕ) :
      ⌊(MixedRadix.radices p.q i : ℝ) * endpoint side (ω i)⌋₊ =
        (digits p hr side ω i : ℕ) := by
    have hq : (0 : ℝ) < MixedRadix.radices p.q i := by exact_mod_cast hr i
    have hf : ⌊(MixedRadix.radices p.q i : ℝ) * endpoint side (ω i)⌋₊ <
        MixedRadix.radices p.q i :=
      (Nat.floor_lt (mul_nonneg hq.le (hunit i).1)).mpr (by nlinarith [(hunit i).2])
    change _ = _ % MixedRadix.radices p.q i
    rw [Nat.mod_eq_of_lt hf]
  exact hp.source_good_event_exclusions j hj (digits p hr false ω) (digits p hr true ω)
    hdx hdy (fun i => (ω i).2.1) (fun i => (ω i).2.2)
    (fun i => (hx i).1) (fun i => (hy i).1)
    (hfloor false hx) (hfloor true hy) hE.1 hE.2.2.1

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_CircleConditionalConvolutionData
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped lp ComplexConjugate
namespace Invariant233.CircleCoupling
open InvariantProjection.ConditionalConvolution
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem conditionalData_of_truncation_mass
    (j : ℕ) (hj : 1 ≤ j) (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hF : ∀ z, IsStarProjection (F z))
    (hFm : ∀ v : Rotation.Fiber, StronglyMeasurable (fun z => F z v))
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun z => F z (ξ z))
    (c : ℝ) (hmass : c ≤ (law p j).real (truncationEvent p j hr
      (fun z => ((F z ProjectionCocycleWindow.basisZero) 0).re))) :
    Nonempty (Data Sample (law p j) (p.K j) (p.coefficientBound j)
      (1 / (j : ℝ)) c (Real.exp (-p.L j)) (Real.exp (-p.L j / 400))) := by
  classical
  let := law_isProbabilityMeasure hp j
  let r : Circle → ℝ := fun z => ((F z ProjectionCocycleWindow.basisZero) 0).re
  let E := truncationEvent p j hr r
  let ξ : Sample → Rotation.Fiber := fun ω =>
    F (point p hr false ω) ProjectionCocycleWindow.basisZero
  let γ : Sample → Rotation.Fiber := fun ω =>
    (1 - F (point p hr true ω)) ProjectionCocycleWindow.basisZero
  let Fx : Sample → ℤ → ℝ := fun ω k => p.floorCocycle θ k (point p hr false ω)
  let Fy : Sample → ℤ → ℝ := fun ω k => p.floorCocycle θ k (point p hr true ω)
  have hrm : Measurable r := Complex.continuous_re.measurable.comp
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 0).continuous.comp_stronglyMeasurable
      (hFm ProjectionCocycleWindow.basisZero)).measurable)
  have hEm : MeasurableSet E := measurableSet_truncationEvent hp j hr hrm
  obtain ⟨H₁, H₂, hm₁, hm₂, hc₁, hc₂, hatt⟩ :=
    tail_exceptional_families_of_subset hp j hj hr E hEm
      (truncationEvent_subset_tagEvent p j hr r)
  have hordered := orderedCouplingIdentities_of_rational hp hr F hF
    (fun k => (hFm (lp.single 2 k 1)).measurable)
    (hp.rational_graphs_of_representation hmem hP hT F hrep) j
  have hbound := hordered.mono (fun _ h k => (h.2 k).2)
  have hzero := hp.ae_parameter_convolution_absolute_and_zero (law p j)
    (point p hr false) (point p hr true) (measurable_point hp hr true).aemeasurable
    (endpoint_absolutelyContinuous hp j hr true) F hF hrep hT
    (hordered.mono (fun _ h => h.1)) hbound
  have hratio := hp.ae_parameter_convolution_ratio_bounds (law p j)
    (point p hr false) (point p hr true) (measurable_point hp hr false).aemeasurable
    (measurable_point hp hr true).aemeasurable
    (endpoint_absolutelyContinuous hp j hr false)
    (endpoint_absolutelyContinuous hp j hr true) hbound
  have hγm : StronglyMeasurable (fun z =>
      (1 - F z) ProjectionCocycleWindow.basisZero) := by
    have h : StronglyMeasurable
        ((fun _ : Circle => ProjectionCocycleWindow.basisZero) -
          fun z => F z ProjectionCocycleWindow.basisZero) :=
      stronglyMeasurable_const.sub (hFm ProjectionCocycleWindow.basisZero)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp only [Pi.sub_apply, sub_apply, one_apply_eq_self]
  refine ⟨{
    mX := endpointSigma p hr false
    mY := endpointSigma p hr true
    mX_le := (measurable_point hp hr false).comap_le
    mY_le := (measurable_point hp hr true).comap_le
    ξ := ξ
    γ := γ
    ξ_measurable := (hFm ProjectionCocycleWindow.basisZero).comp_measurable
      (measurable_iff_comap_le.mpr le_rfl)
    γ_measurable := hγm.comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    ξ_unit := Eventually.of_forall (fun ω =>
      ProjectionCocycleWindow.projection_vector_norm_le _ (hF _))
    γ_unit := Eventually.of_forall (fun ω =>
      ProjectionCocycleWindow.complement_vector_norm_le _ (hF _))
    Fx := Fx
    Fy := Fy
    Fx_measurable := fun k => (hp.measurable_parameter_cocycle k).comp
      (measurable_point hp hr false)
    Fy_measurable := fun k => (hp.measurable_parameter_cocycle k).comp
      (measurable_point hp hr true)
    Fx_pos := Eventually.of_forall (fun ω k => p.floorCocycle_pos θ k _)
    Fy_pos := Eventually.of_forall (fun ω k => p.floorCocycle_pos θ k _)
    Fx_zero := Eventually.of_forall (fun ω => p.floorCocycle_zero θ _)
    Fy_zero := Eventually.of_forall (fun ω => p.floorCocycle_zero θ _)
    zero_convolution := ?_
    ratio_bounds := fun n _ => hratio.mono (fun _ h => h n)
    E := E
    E_measurable := hEm
    E_mass := hmass
    coefficient_bounds := ?_
    H₁ := H₁
    H₂ := H₂
    H₁_measurable := hm₁
    H₂_measurable := hm₂
    attenuation := hatt
    conditional₁ := hc₁
    conditional₂ := hc₂ }⟩
  · intro n _
    filter_upwards [hzero] with ω hω
    exact (hω n ProjectionCocycleWindow.basisZero ProjectionCocycleWindow.basisZero).2
  · filter_upwards [ae_restrict_mem hEm,
      ae_restrict_of_ae (ae_truncationEvent_exclusions hp j hj hr r)] with ω hω he
    have he' := he hω
    have hdiag := hω.2.2.2.2
    have hright : ((F (point p hr true ω) ProjectionCocycleWindow.basisZero) 0).re ≤
        1 - 1 / (j : ℝ) := by
      change 1 / (j : ℝ) ≤ 1 - ((F (point p hr true ω)
        ProjectionCocycleWindow.basisZero) 0).re at hdiag
      linarith
    exact hp.canonical_projection_coefficient_properties j hj _ _
      (fun s hs i hi => (he' s hs i hi).1) (fun s hs i hi => (he' s hs i hi).2)
      _ _ (hF _) (hF _) (1 / (j : ℝ)) hω.2.2.2.1 hright

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleMeasurableObstruction
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace
namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem measurableOperator_hasOnlyTrivialInvariantProjections_oai (hθ : Irrational θ) :
    HasOnlyTrivialInvariantProjections (Rotation.algebra θ) (p.measurableOperator θ hp) := by
  intro P hPm hP hT
  by_cases hP0 : P = 0
  · exact Or.inl hP0
  by_cases hP1 : P = 1
  · exact Or.inr hP1
  exfalso
  let hr := MixedRadix.radices_pos hp.q_pos hp.frequency_increasing hp.frequency_divisible
  obtain ⟨F, hF, _hbound, hFm, hrep, _hgraph, J, hJpos, hmass⟩ :=
    hp.exists_rational_graph_field_with_truncation_mass hθ hr hPm hP hT hP0 hP1
  have hc : (0 : ℝ) < Real.exp (-90) / 2 := by positivity
  have hsmall : ∀ᶠ j : ℕ in atTop, 1 / (j : ℝ) < Real.exp (-90) / 2 :=
    (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds hc)
  obtain ⟨j, hjJ, hjc⟩ := ((eventually_ge_atTop J).and hsmall).exists
  have hj : 1 ≤ j := hJpos.trans hjJ
  have hm : Real.exp (-90) / 2 ≤ (CircleCoupling.law p j).real
      (CircleCoupling.truncationEvent p j hr
        (fun z => ((F z ProjectionCocycleWindow.basisZero) 0).re)) := by
    simpa only [PositiveDiagonalModel.e0, ProjectionCocycleWindow.basisZero,
      lp.inner_single_left, RCLike.inner_apply, star_one, map_one, one_mul, mul_one] using hmass j hjJ
  let := CircleCoupling.law_isProbabilityMeasure hp j
  exact hp.no_conditional_data_at_stage j hj (Real.exp (-90) / 2) hjc
    (CircleCoupling.conditionalData_of_truncation_mass hp j hj hr hPm hP hT
      F hF hFm hrep (Real.exp (-90) / 2) hm)

end Invariant233.CircleParameterLaws

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.CircleParameterLaws.measurableOperator_hasOnlyTrivialInvariantProjections_oai := @OAI.Invariant233.CircleParameterLaws.measurableOperator_hasOnlyTrivialInvariantProjections_oai
