-- Prove2me | solution 1 for OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:34:10.826214+00:00
-- url     : https://prove2.me/submissions/5b0c5bd0-88ec-496e-a27c-2f5047c9e50b

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Algebra.Star.UnitaryStarAlgAut
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
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Group.InfiniteSum
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
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.Data.Finsupp.Option
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Find
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalLExpectation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Group.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProductMeasure
import Mathlib.Tactic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003
import Theorems.Thm_OAI_Invariant233_OrderedProductCoupling_source_circlePairLaw_pairIdentity_of_triangular
import Theorems.Thm_OAI_Invariant233_ProductModel_eventually_actualSource_conditionalData
import Theorems.Thm_OAI_Invariant233_ProductModel_exists_covariantProjectionField_pairIdentity
import Theorems.Thm_OAI_Invariant233_ProductScaleLaws_eventually_source_product_tail_estimate

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ConvolutionUniformConstant
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace InvariantProjection.ConditionalConvolution

theorem Data.obstruction_of_coefficient_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {K : ℕ} {D a c η δ ε : ℝ} (d : Data Ω μ K D a c η δ)
    (hε : 0 ≤ ε)
    (hcoeff : ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖A v‖ ≤ D) →
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖B v‖ ≤ D) →
      a ≤ ‖A 0‖ → a ≤ ‖B 0‖ →
      ∃ n : ℕ, n ≤ 2 * K ∧ ε ≤ ‖truncated K n A B‖)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) :
    c * ε ≤ ((2 * K + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  have hsum : ∀ A B : ℤ → ℂ,
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖A v‖ ≤ D) →
      (∀ v : ℤ, |v| ≤ (K : ℤ) → ‖B v‖ ≤ D) →
      a ≤ ‖A 0‖ → a ≤ ‖B 0‖ →
      ε ≤ ∑ n ∈ Finset.range (2 * K + 1), ‖truncated K n A B‖ := by
    intro A B hA hB hA0 hB0
    obtain ⟨n, hn, hnc⟩ := hcoeff A B hA hB hA0 hB0
    have hnmem : n ∈ Finset.range (2 * K + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hn)
    exact hnc.trans (Finset.single_le_sum
      (fun k (_ : k ∈ Finset.range (2 * K + 1)) => norm_nonneg (truncated K k A B)) hnmem)
  exact d.obstruction_of_pointwise hε hsum hη hδ
    (fun n hn => d.pointwise_truncated_bound n hn hη)

end InvariantProjection.ConditionalConvolution

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

end Invariant233.FieldTraceCyclic

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

theorem orbit_inclusion (W : Aˣ) (D : A)
    (h : (1 - p) * ((W : A) * D) * p = 0) :
    (1 - (↑(W⁻¹) * p * (W : A))) * D * p = 0 := by
  have heq : ↑(W⁻¹) * ((1 - p) * ((W : A) * D) * p) =
      (1 - (↑(W⁻¹) * p * (W : A))) * D * p := by
    simp only [mul_sub, sub_mul, one_mul, mul_assoc]
    simp
  rw [← heq, h, mul_zero]

end Ring


end Invariant233.OrbitInvariance

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductScaleConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Topology
open Filter
namespace Invariant233.ProductScaleLaws

variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem C_pos (n : ℕ) : 0 < p.C n := by
  rw [hp.C_eq n]
  exact lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hp.L_ge_one n))
    (le_max_left _ _)

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterAttenuationConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductScaleData.mem_earlyCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology
namespace Invariant233

namespace ProductScaleLaws
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem conditional_tail_le (n : ℕ) :
    (2 * (p.K n : ℝ) + 1) *
      (Real.exp (-p.L n) + 2 * Real.sqrt (Real.exp (-p.L n / 400))) ≤
      p.ε n / ((n + 1 : ℕ) : ℝ) := by
  apply ConvolutionContradiction.coefficient_tail_le _ _ _ _
    (le_trans (by norm_num : (0 : ℝ) ≤ 1) (hp.L_ge_one n))
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using
    hp.polynomial_attenuation n

theorem not_eventually_conditional_obstruction (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n : ℕ in atTop, c * p.ε n ≤ (2 * (p.K n : ℝ) + 1) *
      (Real.exp (-p.L n) + 2 * Real.sqrt (Real.exp (-p.L n / 400))) := by
  intro h
  have hstage : ∀ᶠ n : ℕ in atTop, 1 / ((n + 1 : ℕ) : ℝ) < c := by
    have ht : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    exact ht.eventually (gt_mem_nhds hc)
  obtain ⟨n, hn, hnc⟩ := (h.and hstage).exists
  exact ConvolutionContradiction.fixed_stage_contradiction c (p.ε n)
    ((n + 1 : ℕ) : ℝ) (hp.epsilon_pos n) hnc (hn.trans (hp.conditional_tail_le n))

end ProductScaleLaws
end Invariant233

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFieldMeasurability
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.StrongField

open MeasureTheory Filter
open scoped Topology

variable {X ι H F : Type*} [MeasurableSpace X] [Countable ι]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem stronglyMeasurable_of_coordinates (b : HilbertBasis ι ℂ H)
    {v : X → H} (hv : ∀ i, StronglyMeasurable fun x => b.repr (v x) i) :
    StronglyMeasurable v := by
  classical
  let approximant : Finset ι → X → H := fun s x =>
    ∑ i ∈ s, b.repr (v x) i • b i
  have hm (s : Finset ι) : StronglyMeasurable (approximant s) := by
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact (hv i).smul_const (b i)
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ι)) hm
  apply tendsto_pi_nhds.mpr
  intro x
  simpa only [HasSum, SummationFilter.unconditional_filter, approximant] using b.hasSum_repr (v x)

theorem stronglyMeasurable_adjoint_apply_of_columns [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (A : X → H →L[ℂ] H)
    (hA : ∀ i, StronglyMeasurable fun x => A x (b i)) (v : H) :
    StronglyMeasurable fun x => (A x).adjoint v := by
  apply stronglyMeasurable_of_coordinates b
  intro i
  simp only [b.repr_apply_apply, ContinuousLinearMap.adjoint_inner_right]
  exact (continuous_id.inner continuous_const).comp_stronglyMeasurable (hA i)

end Invariant233.StrongField

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_FieldOperator
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace Invariant233.DirectIntegral
variable {X E F G : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G]

variable (A : X → E →L[ℂ] F) (C : ℝ)
  (hA : ∀ x, ‖A x‖ ≤ C)
  (hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ)

theorem fieldOperator_ae (f : Lp E 2 μ) :
    fieldOperator A C hA hm f =ᵐ[μ] fun x => A x (f x) :=
  fieldOperatorVec_ae A C hA hm f

variable {A C hA hm}

theorem fieldOperator_comp_of_ae_eq
    {B : X → F →L[ℂ] G} {P : X → E →L[ℂ] G} {D R : ℝ}
    {hB : ∀ x, ‖B x‖ ≤ D} {hP : ∀ x, ‖P x‖ ≤ R}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    {hp : ∀ v, AEStronglyMeasurable (fun x => P x v) μ}
    (heq : P =ᵐ[μ] fun x => (B x).comp (A x)) :
    fieldOperator P R hP hp =
      (fieldOperator B D hB hn).comp (fieldOperator A C hA hm) := by
  ext f
  filter_upwards [fieldOperator_ae P R hP hp f,
    fieldOperator_ae B D hB hn (fieldOperator A C hA hm f),
    fieldOperator_ae A C hA hm f, heq] with x hx hy hz he
  change fieldOperator P R hP hp f x =
    fieldOperator B D hB hn (fieldOperator A C hA hm f) x
  rw [hx, hy, hz, he]
  rfl

theorem fieldOperator_ae_eq_of_eq [IsFiniteMeasure μ] [SeparableSpace E]
    {B : X → E →L[ℂ] F} {D : ℝ} {hB : ∀ x, ‖B x‖ ≤ D}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    (heq : fieldOperator A C hA hm = fieldOperator B D hB hn) : A =ᵐ[μ] B := by
  have hpoint (v : E) : ∀ᵐ x ∂μ, A x v = B x v := by
    have heqv := congrArg (fun T : Lp E 2 μ →L[ℂ] Lp F 2 μ => T (Lp.const 2 μ v)) heq
    have hae : fieldOperator A C hA hm (Lp.const 2 μ v) =ᵐ[μ]
        fieldOperator B D hB hn (Lp.const 2 μ v) := by rw [heqv]
    filter_upwards [fieldOperator_ae A C hA hm (Lp.const 2 μ v),
      fieldOperator_ae B D hB hn (Lp.const 2 μ v), Lp.coeFn_const 2 μ v, hae]
      with x hx hy hv he
    simpa only [hx, hy, hv, Function.const_apply] using he
  have hseq : ∀ᵐ x ∂μ, ∀ n : ℕ, A x (denseSeq E n) = B x (denseSeq E n) :=
    ae_all_iff.mpr fun n => hpoint (denseSeq E n)
  filter_upwards [hseq] with x hx
  have hfunctions : (A x : E → F) = (B x : E → F) :=
    (denseRange_denseSeq E).equalizer (A x).continuous (B x).continuous (funext hx)
  exact DFunLike.ext' hfunctions

end Invariant233.DirectIntegral

namespace Invariant233.DirectIntegral
variable {X E F : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
  {A : X → E →L[ℂ] F} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}
  {hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ}

theorem fieldOperator_adjoint_of_ae_eq
    {B : X → F →L[ℂ] E} {D : ℝ} {hB : ∀ x, ‖B x‖ ≤ D}
    {hn : ∀ v, AEStronglyMeasurable (fun x => B x v) μ}
    (heq : B =ᵐ[μ] fun x => ContinuousLinearMap.adjoint (A x)) :
    fieldOperator B D hB hn = ContinuousLinearMap.adjoint (fieldOperator A C hA hm) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro f g
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fieldOperator_ae B D hB hn f,
    fieldOperator_ae A C hA hm g, heq] with x hx hy he
  rw [hx, hy, he]
  exact (A x).adjoint_inner_left (g x) (f x)

end Invariant233.DirectIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_FieldProjections
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology

namespace Invariant233.DirectIntegral
variable {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [SeparableSpace E]
  {A : X → E →L[ℂ] E} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}
  {hm : ∀ v, AEStronglyMeasurable (fun x => A x v) μ}

theorem ae_isIdempotentElem_of_fieldOperator (hC : 0 ≤ C)
    (hP : IsIdempotentElem (fieldOperator A C hA hm)) :
    ∀ᵐ x ∂μ, IsIdempotentElem (A x) := by
  have hAA : ∀ x, ‖A x * A x‖ ≤ C * C := fun x =>
    (norm_mul_le _ _).trans (mul_le_mul (hA x) (hA x) (norm_nonneg _) hC)
  have hmAA : ∀ v, AEStronglyMeasurable (fun x => (A x * A x) v) μ := fun v =>
    apply_aestronglyMeasurable A hm (hm v)
  have hmul : fieldOperator (fun x => A x * A x) (C * C) hAA hmAA =
      fieldOperator A C hA hm * fieldOperator A C hA hm :=
    fieldOperator_comp_of_ae_eq (Filter.Eventually.of_forall fun x => rfl)
  have hfield := fieldOperator_ae_eq_of_eq (hmul.trans hP.eq)
  exact hfield

end Invariant233.DirectIntegral

namespace Invariant233.DirectIntegral
variable {X E ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [SeparableSpace E] [Countable ι]
  {A : X → E →L[ℂ] E} {C : ℝ} {hA : ∀ x, ‖A x‖ ≤ C}

theorem ae_isSelfAdjoint_of_fieldOperator (b : HilbertBasis ι ℂ E)
    (hm : ∀ v, StronglyMeasurable (fun x => A x v))
    (hP : IsSelfAdjoint (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable))) :
    ∀ᵐ x ∂μ, IsSelfAdjoint (A x) := by
  have hB : ∀ x, ‖star (A x)‖ ≤ C := by
    intro x
    rw [ContinuousLinearMap.star_eq_adjoint, LinearIsometryEquiv.norm_map]
    exact hA x
  have hn : ∀ v, AEStronglyMeasurable (fun x => star (A x) v) μ := by
    intro v
    simpa only [ContinuousLinearMap.star_eq_adjoint] using
      (StrongField.stronglyMeasurable_adjoint_apply_of_columns b A
        (fun i => hm (b i)) v).aestronglyMeasurable
  have hglobal : fieldOperator (fun x => star (A x)) C hB hn =
      star (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable)) := by
    rw [ContinuousLinearMap.star_eq_adjoint]
    exact fieldOperator_adjoint_of_ae_eq (Filter.Eventually.of_forall fun x =>
      ContinuousLinearMap.star_eq_adjoint (A x))
  exact fieldOperator_ae_eq_of_eq (hglobal.trans hP.star_eq)

theorem ae_isStarProjection_of_fieldOperator (b : HilbertBasis ι ℂ E) (hC : 0 ≤ C)
    (hm : ∀ v, StronglyMeasurable (fun x => A x v))
    (hP : IsStarProjection (fieldOperator (μ := μ) A C hA (fun v => (hm v).aestronglyMeasurable))) :
    ∀ᵐ x ∂μ, IsStarProjection (A x) := by
  filter_upwards [ae_isIdempotentElem_of_fieldOperator hC hP.isIdempotentElem,
    ae_isSelfAdjoint_of_fieldOperator b hm hP.isSelfAdjoint] with x hid hself
  exact ⟨hid, hself⟩

end Invariant233.DirectIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ScalarMultiplierFields
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped ENNReal

namespace Invariant233.L2Multiplication

variable {X E : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

variable [IsFiniteMeasure μ]

variable {ι : Type*} [Countable ι] [CompleteSpace E]

omit [IsFiniteMeasure μ] [CompleteSpace E] in

theorem separableSpace_of_countable_hilbertBasis (b : HilbertBasis ι ℂ E) :
    TopologicalSpace.SeparableSpace E := by
  apply TopologicalSpace.isSeparable_univ_iff.mp
  have hs := ((Set.countable_range b).isSeparable.span (R := ℂ)).closure
  rw [← Submodule.topologicalClosure_coe, b.dense_span] at hs
  exact hs

end Invariant233.L2Multiplication

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

end Invariant233.FiniteSupportCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCocycle
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

theorem cocycleVersion_pos {I : Type*} (θ c : I → ℝ) (k : ℤ) (x : Space I) :
    0 < cocycleVersion θ c k x :=
  Real.exp_pos _

end Invariant233.ProductCocycle

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_MixedRadixCircle
attribute [-instance] _root_.OAI.Invariant233.MixedRadix.digitLaw_isProbability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.MixedRadix

@[simp] theorem hybrid_apply_lt {r : ℕ → ℕ} (d e : Digits r) {N n : ℕ} (hn : n < N) :
    hybrid d e N n = e n := ite_eq_left hn

end Invariant233.MixedRadix

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ProjectionDiagonalPropagation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection

open scoped InnerProductSpace
open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem projection_inner_eq_inner_projected {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    ⟪e, P e⟫_ℂ = ⟪P e, P e⟫_ℂ := by
  have hid : P (P e) = P e := by
    exact congrArg (fun A : H →L[ℂ] H => A e) hP.isIdempotentElem
  have hs := hP.isSelfAdjoint.isSymmetric e (P e)
  simpa only [ContinuousLinearMap.coe_coe, hid] using hs.symm

theorem projection_inner_eq_zero_iff {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    ⟪e, P e⟫_ℂ = 0 ↔ P e = 0 := by
  rw [projection_inner_eq_inner_projected hP, inner_self_eq_zero]

omit [CompleteSpace H] in

theorem projection_invariance_apply {P Q D : H →L[ℂ] H}
    (hinv : (1 - Q) * D * P = 0) (v : H) :
    Q (D (P v)) = D (P v) := by
  have h := congrArg (fun A : H →L[ℂ] H => A v) hinv
  simp only [mul_apply_eq_comp, sub_apply,
    one_apply_eq_self, zero_apply, sub_eq_zero] at h
  exact h.symm

theorem projection_kernel_propagation {P Q D : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    {e : H} {a : ℂ} (ha : a ≠ 0)
    (hcoord : ∀ v : H, ⟪e, D v⟫_ℂ = a * ⟪e, v⟫_ℂ)
    (hinv : (1 - Q) * D * P = 0) (hQe : Q e = 0) :
    P e = 0 := by
  apply (projection_inner_eq_zero_iff hP e).mp
  have hfixed := projection_invariance_apply hinv e
  have hz : ⟪e, D (P e)⟫_ℂ = 0 := by
    calc
      ⟪e, D (P e)⟫_ℂ = ⟪e, Q (D (P e))⟫_ℂ := by rw [hfixed]
      _ = ⟪Q e, D (P e)⟫_ℂ := (hQ.isSelfAdjoint.isSymmetric e (D (P e))).symm
      _ = 0 := by rw [hQe, inner_zero_left]
  rw [hcoord] at hz
  exact (mul_eq_zero.mp hz).resolve_left ha

omit [CompleteSpace H] in

theorem projection_fixed_propagation {P Q D : H →L[ℂ] H}
    {e : H} {a : ℂ} (ha : a ≠ 0) (heigen : D e = a • e)
    (hinv : (1 - Q) * D * P = 0) (hPe : P e = e) :
    Q e = e := by
  have hfixed := projection_invariance_apply hinv e
  rw [hPe, heigen, map_smul] at hfixed
  exact (smul_right_injective H ha) hfixed

omit [CompleteSpace H] in
private theorem complex_inner_self_re_eq_norm_sq (v : H) :
    (⟪v, v⟫_ℂ).re = ‖v‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) v

theorem projection_re_inner_eq_zero_iff {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    (⟪e, P e⟫_ℂ).re = 0 ↔ P e = 0 := by
  rw [projection_inner_eq_inner_projected hP, complex_inner_self_re_eq_norm_sq,
    sq_eq_zero_iff, norm_eq_zero]

theorem projection_re_inner_eq_self_iff {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    (⟪e, P e⟫_ℂ).re = ‖e‖ ^ 2 ↔ P e = e := by
  have h := projection_re_inner_eq_zero_iff hP.one_sub e
  simp only [sub_apply, one_apply_eq_self, inner_sub_right,
    Complex.sub_re, complex_inner_self_re_eq_norm_sq, sub_eq_zero] at h
  exact (eq_comm.trans h).trans eq_comm

theorem projection_re_inner_bounds {P : H →L[ℂ] H}
    (hP : IsStarProjection P) (e : H) :
    0 ≤ (⟪e, P e⟫_ℂ).re ∧ (⟪e, P e⟫_ℂ).re ≤ ‖e‖ ^ 2 := by
  have hn : ∀ {Q : H →L[ℂ] H}, IsStarProjection Q → 0 ≤ (⟪e, Q e⟫_ℂ).re := by
    intro Q hQ
    rw [projection_inner_eq_inner_projected hQ]
    exact inner_self_nonneg (𝕜 := ℂ)
  refine ⟨hn hP, ?_⟩
  have hc := hn hP.one_sub
  simp only [sub_apply, one_apply_eq_self, inner_sub_right,
    Complex.sub_re, complex_inner_self_re_eq_norm_sq] at hc
  exact sub_nonneg.mp hc

theorem selfAdjoint_coordinate_law {D : H →L[ℂ] H}
    (hD : IsSelfAdjoint D) {e : H} {a : ℝ}
    (heigen : D e = (a : ℂ) • e) (v : H) :
    ⟪e, D v⟫_ℂ = (a : ℂ) * ⟪e, v⟫_ℂ := by
  calc
    ⟪e, D v⟫_ℂ = ⟪D e, v⟫_ℂ := (hD.isSymmetric e v).symm
    _ = (a : ℂ) * ⟪e, v⟫_ℂ := by
      rw [heigen, inner_smul_left]
      simp

theorem projection_real_diagonal_propagation {P Q D : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hD : IsSelfAdjoint D) {e : H} (he : ‖e‖ = 1)
    {a : ℝ} (ha : a ≠ 0) (heigen : D e = (a : ℂ) • e)
    (hinv : (1 - Q) * D * P = 0) :
    ((⟪e, Q e⟫_ℂ).re = 0 → (⟪e, P e⟫_ℂ).re = 0) ∧
    ((⟪e, P e⟫_ℂ).re = 1 → (⟪e, Q e⟫_ℂ).re = 1) := by
  have hac : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
  constructor
  · intro h
    exact (projection_re_inner_eq_zero_iff hP e).mpr
      (projection_kernel_propagation hP hQ hac
        (selfAdjoint_coordinate_law hD heigen) hinv
        ((projection_re_inner_eq_zero_iff hQ e).mp h))
  · intro h
    have hPe : P e = e := (projection_re_inner_eq_self_iff hP e).mp (by simpa [he] using h)
    have hQe := projection_fixed_propagation hac heigen hinv hPe
    simpa [he] using (projection_re_inner_eq_self_iff hQ e).mpr hQe

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_ProjectionAtomOrbit
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped InnerProductSpace ComplexOrder
namespace Invariant233.ProjectionAtomOrbit

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}

theorem vectorTrace_pos_of_faithful (ξ : H)
    (hξ : IsFaithfulTracialVector M ξ)
    {p : H →L[ℂ] H} (hp : p ∈ M) (hproj : IsStarProjection p) (hne : p ≠ 0) :
    0 < (vectorTrace ξ p).re := by
  have hpositive := ContinuousLinearMap.IsPositive.of_isStarProjection hproj
  have hnonneg : 0 ≤ vectorTrace ξ p := hpositive.inner_nonneg_right ξ
  have hparts := Complex.nonneg_iff.mp hnonneg
  by_contra h
  apply hne
  apply hξ.2.2 p hp hpositive
  apply Complex.ext
  · exact le_antisymm (not_lt.mp h) hparts.1
  · exact hparts.2.symm

end Invariant233.ProjectionAtomOrbit

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductCovariance
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductProjectionFields
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.ProductModel

theorem projection_vectorTrace_mem_Ioo {θ : ℕ → ℝ} {P : Hilbert →L[ℂ] Hilbert}
    (hP : P ∈ factor θ) (hp : IsStarProjection P) (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    0 < (vectorTrace traceVector P).re ∧ (vectorTrace traceVector P).re < 1 := by
  have htrace := traceVector_faithfulTracial θ
  have hpos := ProjectionAtomOrbit.vectorTrace_pos_of_faithful traceVector htrace hP hp hP0
  have hcomp : 1 - P ∈ factor θ := sub_mem (one_mem _) hP
  have hcomp0 : (1 : Hilbert →L[ℂ] Hilbert) - P ≠ 0 := by
    intro h
    exact hP1 (sub_eq_zero.mp h).symm
  have hposcomp := ProjectionAtomOrbit.vectorTrace_pos_of_faithful
    traceVector htrace hcomp hp.one_sub hcomp0
  have hn : ‖traceVector‖ = 1 := htrace.1
  have heq : (vectorTrace traceVector (1 - P)).re =
      1 - (vectorTrace traceVector P).re := by
    simp [vectorTrace, inner_sub_right, inner_self_eq_norm_sq_to_K, hn]
  rw [heq] at hposcomp
  exact ⟨hpos, sub_pos.mp hposcomp⟩

end Invariant233.ProductModel

end

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

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductObstructionConstant
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology
open InvariantProjection.ConditionalConvolution

namespace Invariant233.ProductScaleLaws
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem conditional_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) {c η δ : ℝ}
    (d : Data Ω μ (p.K n) (p.coefficientBound n)
      (1 / ((n + 1 : ℕ) : ℝ)) c η δ)
    (hη : 0 ≤ η) (hδ : 0 ≤ δ) :
    c * p.ε n ≤ ((2 * p.K n + 1 : ℕ) : ℝ) * (η + 2 * Real.sqrt δ) := by
  apply d.obstruction_of_coefficient_bound (hp.epsilon_pos n).le _ hη hδ
  exact hp.polynomial_lower n

theorem not_eventually_conditional_data
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (c : ℝ) (hc : 0 < c) :
    ¬ ∀ᶠ n in atTop,
      Nonempty (Data (Ω n) (μ n) (p.K n) (p.coefficientBound n)
        (1 / ((n + 1 : ℕ) : ℝ)) c
        (Real.exp (-p.L n)) (Real.exp (-p.L n / 400))) := by
  intro h
  apply hp.not_eventually_conditional_obstruction c hc
  filter_upwards [h] with n hn
  obtain ⟨d⟩ := hn
  have hb := hp.conditional_bound n d (Real.exp_pos _).le (Real.exp_pos _).le
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hb

end Invariant233.ProductScaleLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_BlockPhaseConstruction
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology

namespace Invariant233.ProductPhases

theorem mem_consecutiveBlock_iff (m : ℕ → ℕ) (j i : ℕ) :
    i ∈ consecutiveBlock m j ↔
      (∑ r ∈ Finset.range j, m r) ≤ i ∧
        i < (∑ r ∈ Finset.range j, m r) + m j := by
  simp [consecutiveBlock]

theorem mem_consecutiveBlock_enumeration (m : ℕ → ℕ)
    (e : ℕ ≃ Σ j, Fin (m j))
    (he : ∀ a : Σ j, Fin (m j),
      e.symm a = (∑ r ∈ Finset.range a.1, m r) + a.2.val)
    (i : ℕ) : i ∈ consecutiveBlock m (e i).1 := by
  have hi : i = (∑ r ∈ Finset.range (e i).1, m r) + (e i).2.val := by
    simpa only [e.symm_apply_apply] using he (e i)
  apply (mem_consecutiveBlock_iff m (e i).1 i).mpr
  have hb := (e i).2.isLt
  omega

end Invariant233.ProductPhases

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_IndependentRotation
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open MeasureTheory

namespace Invariant233.IndependentRotation

theorem irrational_finsupp_rat_sum {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (c : ι →₀ ℚ) (hc : c ≠ 0) :
    Irrational (c.sum (fun i q => (q : ℝ) * θ i)) := by
  rintro ⟨r, hr⟩
  let l : Option ι →₀ ℚ := c.optionElim (-r)
  have hl : Finsupp.linearCombination ℚ (fun o : Option ι => o.elim 1 θ) l = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum_option_index_smul]
    simp only [l, Finsupp.optionElim_apply_eq_elim, Option.elim_none,
      Finsupp.some_optionElim, Option.elim_some, Rat.smul_def, Rat.cast_neg, mul_one]
    linarith
  exact (Finsupp.optionElim_ne_zero_of_right (-r) c hc)
    ((linearIndependent_iff.mp hθ) l hl)

theorem irrational_finsupp_int_sum {ι : Type*} {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (hv : v ≠ 0) :
    Irrational (v.sum (fun i n => (n : ℝ) * θ i)) := by
  let c : ι →₀ ℚ := v.mapRange (fun n : ℤ => (n : ℚ)) (by simp)
  have hc : c ≠ 0 := by
    intro h
    apply hv
    ext i
    have hi := DFunLike.congr_fun h i
    dsimp [c] at hi
    exact_mod_cast hi
  have h := irrational_finsupp_rat_sum hθ c hc
  simpa [c, Finsupp.sum_mapRange_index] using h

end Invariant233.IndependentRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Couplings_ProductSourceConditionalData
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.ProductModel
open OrderedProductCoupling
open InvariantProjection.ConditionalConvolution

theorem actualSource_projection_contradiction
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ) (hθ0 : ∀ i, 0 ≤ θ i) (hθsum : Summable θ)
    (hphase : ∀ i, θ i ∈ Set.Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (A : Hilbert →L[ℂ] Hilbert) (F : Base → Fiber →L[ℂ] Fiber)
    (hF : IsCovariantFieldRepresentation θ A F 1)
    (hproj : ∀ x, IsStarProjection (F x))
    (hinv : (1 - A) * weightedOperator θ (fun i => p.C (e i).1) * A = 0)
    (hdiag : ∀ᵐ x ∂baseMeasure,
      0 < BlockedProductCoupling.projectionDiagonal F x ∧
      BlockedProductCoupling.projectionDiagonal F x < 1)
    (hpair : ∀ j, ∀ᵐ xy ∂circlePairLaw (actualSourceParameters hp e j),
      PairIdentity θ (fun i => p.C (e i).1) F xy)
    (htail : ∀ᶠ j in atTop,
      SourceTailEstimate p e θ j (actualSourceParameters hp e j)) : False := by
  apply hp.not_eventually_conditional_data
    (fun j => law (actualSourceParameters hp e j)) (Real.exp (-82) / 2) (by positivity)
  exact eventually_actualSource_conditionalData hp e he θ hθ0 hθsum hphase A F
    hF hproj hinv hdiag hpair htail

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ErgodicCharacterCriterion
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace Invariant233.Characters

theorem integral_eq_zero_of_eigenfunction {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {σ : X → X} (hσ : MeasurePreserving σ μ μ)
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {z : ℂ} (hz : z ≠ 1)
    (heigen : ∀ᵐ x ∂μ, f (σ x) = z * f x) :
    (∫ x, f x ∂μ) = 0 := by
  have hfm : AEStronglyMeasurable f (μ.map σ) := by rwa [hσ.map_eq]
  have hmap := integral_map hσ.measurable.aemeasurable hfm
  rw [hσ.map_eq] at hmap
  have heq : (∫ x, f x ∂μ) = z * ∫ x, f x ∂μ := by
    calc
      _ = ∫ x, f (σ x) ∂μ := hmap
      _ = ∫ x, z * f x ∂μ := integral_congr_ae heigen
      _ = _ := integral_const_mul z f
  have hzero : (1 - z) * (∫ x, f x ∂μ) = 0 := by
    calc
      _ = (∫ x, f x ∂μ) - z * (∫ x, f x ∂μ) := by ring
      _ = 0 := sub_eq_zero.mpr heq
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hz.symm)

theorem eq_zero_of_dense_inner {E ι : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (v : E) (χ : ι → E)
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hinner : ∀ i, inner ℂ v (χ i) = 0) : v = 0 := by
  let L : E →L[ℂ] ℂ := innerSL ℂ v
  have hspan : Submodule.span ℂ (Set.range χ) ≤ L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hinner i
  have htop := (Submodule.span ℂ (Set.range χ)).topologicalClosure_minimal
    hspan L.isClosed_ker
  rw [hdense] at htop
  have hv : L v = 0 := htop (Submodule.mem_top : v ∈ (⊤ : Submodule ℂ E))
  exact inner_self_eq_zero.mp hv

theorem ergodic_of_dense_L2_eigenfunctions {X ι : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {σ : X → X}
    (hσ : MeasurePreserving σ μ μ) (i₀ : ι) (χ : ι → X → ℂ) (z : ι → ℂ)
    (hχ : ∀ i, MemLp (χ i) 2 μ)
    (hconst : χ i₀ =ᵐ[μ] fun _ => 1)
    (hdense : (Submodule.span ℂ
      (Set.range (fun i => (hχ i).toLp (χ i)))).topologicalClosure = ⊤)
    (hz : ∀ i, i ≠ i₀ → z i ≠ 1)
    (heigen : ∀ i, i ≠ i₀ → ∀ᵐ x ∂μ, χ i (σ x) = z i * χ i x) :
    Ergodic σ μ := by
  classical
  refine ⟨hσ, ⟨?_⟩⟩
  intro s hs hinv
  let p : ℝ := μ.real s
  let u : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) 1
  let e : Lp ℂ 2 μ := indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) 1
  have hσs : MeasurePreserving σ (μ.restrict s) (μ.restrict s) := by
    simpa only [hinv] using hσ.restrict_preimage hs
  have hpair : ∀ i,
      inner ℂ u ((hχ i).toLp (χ i)) = (p : ℂ) * inner ℂ e ((hχ i).toLp (χ i)) := by
    intro i
    have hfull : inner ℂ e ((hχ i).toLp (χ i)) = ∫ x, χ i x ∂μ := by
      rw [L2.inner_indicatorConstLp_one, setIntegral_univ]
      exact integral_congr_ae (hχ i).coeFn_toLp
    have hset : inner ℂ u ((hχ i).toLp (χ i)) = ∫ x in s, χ i x ∂μ := by
      rw [L2.inner_indicatorConstLp_one]
      exact integral_congr_ae ((hχ i).coeFn_toLp.filter_mono (ae_mono Measure.restrict_le_self))
    rw [hfull, hset]
    by_cases hi : i = i₀
    · subst i
      rw [integral_congr_ae hconst,
        integral_congr_ae (hconst.filter_mono (ae_mono Measure.restrict_le_self))]
      simp [p]
    · have hzero := integral_eq_zero_of_eigenfunction hσ (hχ i).aestronglyMeasurable
        (hz i hi) (heigen i hi)
      have hzeros := integral_eq_zero_of_eigenfunction hσs
        (hχ i).aestronglyMeasurable.restrict (hz i hi)
        ((heigen i hi).filter_mono (ae_mono Measure.restrict_le_self))
      rw [hzero, hzeros, mul_zero]
  have heq : u = (p : ℂ) • e := by
    apply sub_eq_zero.mp
    apply eq_zero_of_dense_inner (u - (p : ℂ) • e)
      (fun i => (hχ i).toLp (χ i)) hdense
    intro i
    rw [inner_sub_left, inner_smul_left, hpair i]
    simp
  have huu : inner ℂ u u = (p : ℂ) := by
    change inner ℂ (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ))
      (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_indicatorConstLp]
    simp [p]
  have heu : inner ℂ e u = (p : ℂ) := by
    change inner ℂ (indicatorConstLp 2 MeasurableSet.univ (measure_ne_top μ univ) (1 : ℂ))
      (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)) = _
    rw [L2.inner_indicatorConstLp_indicatorConstLp]
    simp [p]
  have hpalg := congrArg (fun v : Lp ℂ 2 μ => inner ℂ v u) heq
  rw [huu, inner_smul_left, heu] at hpalg
  have hpalg' := congrArg Complex.re hpalg
  simp at hpalg'
  have hp01 : p = 0 ∨ p = 1 := by
    have hpzero : p * (p - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hpzero with hp | hp
    · exact Or.inl hp
    · exact Or.inr (sub_eq_zero.mp hp)
  apply eventuallyConst_set.mpr
  rcases hp01 with hp | hp
  · right
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (measureReal_eq_zero_iff (μ := μ)).mp hp
  · left
    rw [ae_iff]
    have hpc : μ.real sᶜ = 0 := by rw [measureReal_compl hs, probReal_univ]; exact sub_eq_zero.mpr hp.symm
    exact (measureReal_eq_zero_iff (μ := μ)).mp hpc

theorem ergodic_of_dense_continuous_eigenfunctions {X ι : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] [μ.WeaklyRegular]
    {σ : X → X} (hσ : MeasurePreserving σ μ μ)
    (i₀ : ι) (χ : ι → C(X, ℂ)) (z : ι → ℂ)
    (hconst : χ i₀ = 1)
    (hdense : (Submodule.span ℂ (Set.range χ)).topologicalClosure = ⊤)
    (hz : ∀ i, i ≠ i₀ → z i ≠ 1)
    (heigen : ∀ i, i ≠ i₀ → ∀ x, χ i (σ x) = z i * χ i x) :
    Ergodic σ μ := by
  let hχ : ∀ i, MemLp (χ i) 2 μ := fun i => ContinuousMap.memLp μ ℂ (χ i)
  have hlp : (fun i => (hχ i).toLp (χ i)) =
      (fun i => ContinuousMap.toLp 2 μ ℂ (χ i)) := by
    funext i
    apply Lp.ext
    exact (hχ i).coeFn_toLp.trans (ContinuousMap.coeFn_toLp μ (χ i)).symm
  have hdenseLp : (Submodule.span ℂ
      (Set.range (fun i => (hχ i).toLp (χ i)))).topologicalClosure = ⊤ := by
    rw [hlp]
    have hd := (ContinuousMap.toLp_denseRange ℂ μ ℂ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).topologicalClosure_map_submodule hdense
    rw [Submodule.map_span, ← Set.range_comp'] at hd
    exact hd
  refine ergodic_of_dense_L2_eigenfunctions hσ i₀ (fun i => χ i) z hχ ?_ hdenseLp hz ?_
  · exact Eventually.of_forall fun x => by rw [hconst]; rfl
  · intro i hi
    exact Eventually.of_forall (heigen i hi)

end Invariant233.Characters

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_ProductCharacters
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.ProductRotation

open scoped BigOperators ComplexConjugate
open Set Algebra Submodule

variable {ι : Type*}

theorem characterPhase_add (v : ι →₀ ℤ) (x y : ι → UnitAddCircle) :
    characterPhase v (x + y) = characterPhase v x + characterPhase v y := by
  simp [characterPhase, Finsupp.sum_add]

theorem characterPhase_add_index (v w : ι →₀ ℤ) (x : ι → UnitAddCircle) :
    characterPhase (v + w) x = characterPhase v x + characterPhase w x := by
  classical
  simp [characterPhase, Finsupp.sum_add_index, add_zsmul]

theorem productCharacter_add (v : ι →₀ ℤ) (x y : ι → UnitAddCircle) :
    productCharacter v (x + y) = productCharacter v x * productCharacter v y := by
  simp [productCharacter, characterPhase_add, AddCircle.toCircle_add]

theorem productCharacter_add_index (v w : ι →₀ ℤ) :
    productCharacter (v + w) = productCharacter v * productCharacter w := by
  ext x
  simp [productCharacter, characterPhase_add_index, AddCircle.toCircle_add]

theorem productCharacter_neg (v : ι →₀ ℤ) :
    productCharacter (-v) = star (productCharacter v) := by
  ext x
  simp [productCharacter, characterPhase, Finsupp.sum_neg_index,
    Finsupp.sum_neg, AddCircle.toCircle_neg]
  exact Circle.coe_inv_eq_conj _

theorem productFourierAlgebra_separatesPoints :
    (productFourierAlgebra ι).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hxy
  refine ⟨_, ⟨productCharacter (Finsupp.single i 1),
    StarAlgebra.subset_adjoin ℂ _ ⟨Finsupp.single i 1, rfl⟩, rfl⟩, ?_⟩
  intro heq
  apply hi
  apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
  apply Subtype.coe_injective
  simpa only [productCharacter_single_one] using heq

theorem productFourierAlgebra_closure_eq_top :
    (productFourierAlgebra ι).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _
    productFourierAlgebra_separatesPoints

theorem productFourierAlgebra_toSubmodule :
    (productFourierAlgebra ι).toSubalgebra.toSubmodule =
      Submodule.span ℂ (Set.range (productCharacter (ι := ι))) := by
  classical
  rw [productFourierAlgebra, StarAlgebra.adjoin_eq_span]
  congr 1
  apply Set.Subset.antisymm
  · intro f hf
    induction hf using Submonoid.closure_induction with
    | mem f hf =>
      rcases hf with hf | hf
      · exact hf
      · obtain ⟨v, hv⟩ := hf
        exact ⟨-v, by rw [productCharacter_neg, hv, star_star]⟩
    | one => exact ⟨0, productCharacter_zero⟩
    | mul f g hf hg ihf ihg =>
      obtain ⟨v, rfl⟩ := ihf
      obtain ⟨w, rfl⟩ := ihg
      exact ⟨v + w, productCharacter_add_index v w⟩
  · intro f hf
    exact Submonoid.subset_closure (Or.inl hf)

theorem span_productCharacter_closure_eq_top :
    (Submodule.span ℂ (Set.range (productCharacter (ι := ι)))).topologicalClosure = ⊤ := by
  rw [← productFourierAlgebra_toSubmodule]
  exact congr_arg (fun A : StarSubalgebra ℂ C((ι → UnitAddCircle), ℂ) =>
    A.toSubalgebra.toSubmodule) productFourierAlgebra_closure_eq_top

theorem mul_sum_ne_int (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {v : ι →₀ ℤ} (hv : v ≠ 0) {q : ℤ} (hq : q ≠ 0) (k : ℤ) :
    (q : ℝ) * v.sum (fun i z => (z : ℝ) * θ i) ≠ (k : ℝ) := by
  intro heq
  have hz : q • v = 0 := hθ (q • v) k (by
    rw [Finsupp.sum_smul_index (fun _ => by simp)]
    simpa only [Int.cast_mul, mul_assoc, Finsupp.sum, Finset.mul_sum] using heq)
  exact (smul_ne_zero hq hv) hz

theorem characterPhase_coe (v : ι →₀ ℤ) (θ : ι → ℝ) :
    characterPhase v (fun i => (θ i : UnitAddCircle)) =
      ((v.sum (fun i z => (z : ℝ) * θ i) : ℝ) : UnitAddCircle) := by
  change v.sum (fun i n => n • (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (θ i)) =
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ)))
      (v.sum (fun i z => (z : ℝ) * θ i))
  rw [map_finsuppSum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [zsmul_eq_mul] using
    (map_zsmul (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))) (v i) (θ i)).symm

theorem productCharacter_ne_one (θ : ι → ℝ)
    (hθ : ∀ (v : ι →₀ ℤ) (k : ℤ),
      v.sum (fun i z => (z : ℝ) * θ i) = k → v = 0)
    {v : ι →₀ ℤ} (hv : v ≠ 0) {q : ℤ} (hq : q ≠ 0) :
    productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) ≠ 1 := by
  intro heq
  have hphase : characterPhase v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) = 0 := by
    apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
    apply Subtype.coe_injective
    simpa [productCharacter] using heq
  rw [characterPhase_coe, AddCircle.coe_eq_zero_iff] at hphase
  obtain ⟨k, hk⟩ := hphase
  apply mul_sum_ne_int θ hθ hv hq k
  simpa only [Finsupp.sum, Finset.mul_sum, zsmul_eq_mul, mul_one,
    mul_left_comm, mul_assoc] using hk.symm

theorem productCharacter_translation (v : ι →₀ ℤ) (θ : ι → ℝ) (q : ℤ)
    (x : ι → UnitAddCircle) :
    productCharacter v (fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) =
      productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)) *
        productCharacter v x := by
  rw [mul_comm, ← productCharacter_add]
  congr 1

end InvariantProjection.ProductRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductErgodicity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection.ProductRotation

open MeasureTheory

variable {ι : Type*}

theorem integer_affine_independent {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    (v : ι →₀ ℤ) (m : ℤ)
    (heq : v.sum (fun i z => (z : ℝ) * θ i) = m) : v = 0 := by
  by_contra hv
  exact (Invariant233.IndependentRotation.irrational_finsupp_int_sum hθ v hv).ne_int m heq

theorem measurePreserving_product_translation (a : ι → UnitAddCircle) :
    MeasurePreserving (fun x : ι → UnitAddCircle => x + a)
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle)))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  have hcoord (i : ι) : MeasurePreserving
      (fun x : UnitAddCircle => x + a i) volume volume :=
    measurePreserving_add_right volume _
  refine ⟨Measurable.of_eval (fun i => (measurable_pi_apply i).add_const _), ?_⟩
  change (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))).map
      (fun x i => x i + a i) = _
  rw [Measure.infinitePi_map_pi _ (fun i => (hcoord i).measurable)]
  simp only [(hcoord _).map_eq]

theorem product_rotation_integer_ergodic [Countable ι] {θ : ι → ℝ}
    (hθ : LinearIndependent ℚ (fun o : Option ι => o.elim 1 θ))
    {q : ℤ} (hq : q ≠ 0) :
    Ergodic (fun x : ι → UnitAddCircle =>
      fun i => x i + (((q : ℝ) * θ i : ℝ) : UnitAddCircle))
      (Measure.infinitePi (fun _ : ι => (volume : Measure UnitAddCircle))) := by
  let : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
    ⟨UnitAddCircle.measure_univ⟩
  apply Invariant233.Characters.ergodic_of_dense_continuous_eigenfunctions
    (measurePreserving_product_translation (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)))
    (0 : ι →₀ ℤ) productCharacter
    (fun v => productCharacter v (fun i => (((q : ℝ) * θ i : ℝ) : UnitAddCircle)))
    productCharacter_zero span_productCharacter_closure_eq_top
  · intro v hv
    exact productCharacter_ne_one θ (integer_affine_independent hθ) hv hq
  · intro v _ x
    exact productCharacter_translation v θ q x

end InvariantProjection.ProductRotation

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductBaseDynamics
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.ProductModel

open MeasureTheory

theorem rotationIterate_ergodic {θ : ℕ → ℝ}
    (hθ : JointlyRationallyIndependent θ) {k : ℤ} (hk : k ≠ 0) :
    Ergodic (rotationIterate θ k) baseMeasure :=
  InvariantProjection.ProductRotation.product_rotation_integer_ergodic hθ hk

end Invariant233.ProductModel

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_PositiveDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set

namespace Invariant233.Fields

theorem ae_strict_diagonal_of_ergodic
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {σ : Y → Y} (hσ : Ergodic σ μ) {r : Y → ℝ}
    (hr : Measurable r)
    (hrange : ∀ᵐ y ∂μ, 0 ≤ r y ∧ r y ≤ 1)
    (hmean0 : 0 < ∫ y, r y ∂μ) (hmean1 : (∫ y, r y ∂μ) < 1)
    (hzero : ∀ᵐ y ∂μ, r (σ y) = 0 → r y = 0)
    (hone : ∀ᵐ y ∂μ, r y = 1 → r (σ y) = 1) :
    ∀ᵐ y ∂μ, 0 < r y ∧ r y < 1 := by
  have hmeas0 : MeasurableSet {y | r y = 0} := hr (measurableSet_singleton 0)
  have hmeas1 : MeasurableSet {y | r y = 1} := hr (measurableSet_singleton 1)
  have hz : ∀ᵐ y ∂μ, r y ≠ 0 := by
    rcases hσ.ae_empty_or_univ_of_preimage_ae_le hmeas0.nullMeasurableSet hzero with h | h
    · filter_upwards [h] with y hy
      change (r y = 0) = False at hy
      exact fun hz => hy ▸ hz
    · have heq : r =ᵐ[μ] fun _ => 0 := by
        filter_upwards [h] with y hy
        change (r y = 0) = True at hy
        exact hy.symm ▸ True.intro
      have hi : (∫ y, r y ∂μ) = 0 := by
        rw [integral_congr_ae heq]
        simp
      linarith
  have ho : ∀ᵐ y ∂μ, r y ≠ 1 := by
    rcases hσ.ae_empty_or_univ_of_ae_le_preimage hmeas1.nullMeasurableSet hone with h | h
    · filter_upwards [h] with y hy
      change (r y = 1) = False at hy
      exact fun hz => hy ▸ hz
    · have heq : r =ᵐ[μ] fun _ => 1 := by
        filter_upwards [h] with y hy
        change (r y = 1) = True at hy
        exact hy.symm ▸ True.intro
      have hi : (∫ y, r y ∂μ) = 1 := by
        rw [integral_congr_ae heq]
        simp
      linarith
  filter_upwards [hrange, hz, ho] with y hy hy0 hy1
  exact ⟨lt_of_le_of_ne hy.1 (Ne.symm hy0), lt_of_le_of_ne hy.2 hy1⟩

end Invariant233.Fields

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_PositiveDiagonalFields
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter
open scoped InnerProductSpace

namespace Invariant233.Fields

theorem ae_strict_projection_diagonal
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {σ : Y → Y} (hσ : Ergodic σ μ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p D : Y → H →L[ℂ] H} {e : H} (he : ‖e‖ = 1) {f : Y → ℝ}
    (hp : ∀ᵐ y ∂μ, IsStarProjection (p y))
    (hD : ∀ᵐ y ∂μ, IsSelfAdjoint (D y))
    (hf : ∀ᵐ y ∂μ, f y ≠ 0)
    (heigen : ∀ᵐ y ∂μ, D y e = (f y : ℂ) • e)
    (hinv : ∀ᵐ y ∂μ, (1 - p (σ y)) * D y * p y = 0)
    (hr : Measurable fun y => (⟪e, p y e⟫_ℂ).re)
    (hmean0 : 0 < ∫ y, (⟪e, p y e⟫_ℂ).re ∂μ)
    (hmean1 : (∫ y, (⟪e, p y e⟫_ℂ).re ∂μ) < 1) :
    ∀ᵐ y ∂μ, 0 < (⟪e, p y e⟫_ℂ).re ∧ (⟪e, p y e⟫_ℂ).re < 1 := by
  have hps : ∀ᵐ y ∂μ, IsStarProjection (p (σ y)) :=
    hσ.toMeasurePreserving.quasiMeasurePreserving.ae hp
  have hprop : ∀ᵐ y ∂μ,
      ((⟪e, p (σ y) e⟫_ℂ).re = 0 → (⟪e, p y e⟫_ℂ).re = 0) ∧
      ((⟪e, p y e⟫_ℂ).re = 1 → (⟪e, p (σ y) e⟫_ℂ).re = 1) := by
    filter_upwards [hp, hps, hD, hf, heigen, hinv] with y hpy hpsy hDy hfy hey hiy
    exact InvariantProjection.projection_real_diagonal_propagation
      hpy hpsy hDy he hfy hey hiy
  apply ae_strict_diagonal_of_ergodic hσ hr ?_ hmean0 hmean1
    (hprop.mono fun _ h => h.1) (hprop.mono fun _ h => h.2)
  filter_upwards [hp] with y hpy
  simpa only [he, one_pow] using InvariantProjection.projection_re_inner_bounds hpy e

theorem ae_strict_projection_diagonal_of_weighted_shift
    {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
    {σ : Y → Y} (hσ : Ergodic σ μ)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p D : Y → H →L[ℂ] H} (S : (H →L[ℂ] H)ˣ)
    {e : H} (he : ‖e‖ = 1) {f : Y → ℝ}
    (hp : ∀ᵐ y ∂μ, IsStarProjection (p y))
    (hD : ∀ᵐ y ∂μ, IsSelfAdjoint (D y))
    (hf : ∀ᵐ y ∂μ, f y ≠ 0)
    (heigen : ∀ᵐ y ∂μ, D y e = (f y : ℂ) • e)
    (hcov : ∀ᵐ y ∂μ, p (σ y) = ↑(S⁻¹) * p y * (S : H →L[ℂ] H))
    (hinv : ∀ᵐ y ∂μ, (1 - p y) * ((S : H →L[ℂ] H) * D y) * p y = 0)
    (hr : Measurable fun y => (⟪e, p y e⟫_ℂ).re)
    (hmean0 : 0 < ∫ y, (⟪e, p y e⟫_ℂ).re ∂μ)
    (hmean1 : (∫ y, (⟪e, p y e⟫_ℂ).re ∂μ) < 1) :
    ∀ᵐ y ∂μ, 0 < (⟪e, p y e⟫_ℂ).re ∧ (⟪e, p y e⟫_ℂ).re < 1 := by
  apply ae_strict_projection_diagonal hσ he hp hD hf heigen ?_ hr hmean0 hmean1
  filter_upwards [hcov, hinv] with y hcy hiy
  rw [hcy]
  exact OrbitInvariance.orbit_inclusion S (D y) hiy

end Invariant233.Fields

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RepresentedPositiveDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped InnerProductSpace ENNReal

namespace Invariant233.DirectIntegral

variable {Y E ι : Type*} [MeasurableSpace Y] {μ : Measure Y}
  [IsFiniteMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [Countable ι]

theorem ae_invariant_of_represented_invariant
    (b : HilbertBasis ι ℂ E)
    (P T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (p W : Y → E →L[ℂ] E)
    (hP : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun y => W y (ξ y))
    (hinv : (1 - P) * T * P = 0) :
    ∀ᵐ y ∂μ, (1 - p y) * W y * p y = 0 := by
  apply L2Multiplication.field_unique_of_representation b
    ((1 - P) * T * P) (fun y => (1 - p y) * W y * p y) (fun _ => 0)
  · intro ξ
    filter_upwards [hP ξ, hT (P ξ), hP (T (P ξ)),
      Lp.coeFn_sub (T (P ξ)) (P (T (P ξ)))] with y hp ht hpp hsub
    change ((T (P ξ) - P (T (P ξ))) y) =
      W y (p y (ξ y)) - p y (W y (p y (ξ y)))
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [ht, hpp, ht, hp]
  · intro ξ
    rw [hinv]
    filter_upwards [Lp.coeFn_zero E 2 μ] with y hy
    exact hy

variable [CompleteSpace E]

theorem ae_isStarProjection_of_representation
    (b : HilbertBasis ι ℂ E)
    (P : Lp E 2 μ →L[ℂ] Lp E 2 μ) (p : Y → E →L[ℂ] E)
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ y, ‖p y‖ ≤ C)
    (hm : ∀ v, StronglyMeasurable fun y => p y v)
    (hrep : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hP : IsStarProjection P) : ∀ᵐ y ∂μ, IsStarProjection (p y) := by
  let := L2Multiplication.separableSpace_of_countable_hilbertBasis b
  have heq : P = fieldOperator p C hbound (fun v => (hm v).aestronglyMeasurable) := by
    ext ξ
    exact (hrep ξ).trans (fieldOperator_ae p C hbound
      (fun v => (hm v).aestronglyMeasurable) ξ).symm
  apply ae_isStarProjection_of_fieldOperator b hC hm
  rw [← heq]
  exact hP

omit [CompleteSpace E] in

theorem real_constant_vector_state_eq_integral
    (P : Lp E 2 μ →L[ℂ] Lp E 2 μ) (p : Y → E →L[ℂ] E)
    (hrep : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun y => p y (ξ y)) (e : E) :
    (inner ℂ (Lp.const 2 μ e) (P (Lp.const 2 μ e))).re =
      ∫ y, (inner ℂ e (p y e)).re ∂μ := by
  have hi : Integrable (fun y => inner ℂ e (p y e)) μ := by
    apply (L2.integrable_inner (𝕜 := ℂ) (Lp.const 2 μ e)
      (P (Lp.const 2 μ e))).congr
    filter_upwards [Lp.coeFn_const 2 μ e, hrep (Lp.const 2 μ e)] with y he hp
    rw [hp, he]
    rfl
  rw [FieldTraceCyclic.constant_vector_state_eq_integral P p hrep e]
  exact (integral_re hi).symm

end Invariant233.DirectIntegral

namespace Invariant233.Fields

variable {Y E ι : Type*} [MeasurableSpace Y] {μ : Measure Y}
  [IsProbabilityMeasure μ] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Countable ι]

theorem ae_strict_diagonal_of_represented_weighted_shift
    (b : HilbertBasis ι ℂ E) {σ : Y → Y} (hσ : Ergodic σ μ)
    (P T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (p D : Y → E →L[ℂ] E)
    (S : (E →L[ℂ] E)ˣ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y, ‖p y‖ ≤ C)
    (hm : ∀ v, StronglyMeasurable fun y => p y v)
    (hp : ∀ ξ : Lp E 2 μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun y =>
      ((S : E →L[ℂ] E) * D y) (ξ y))
    (hP : IsStarProjection P) (hinv : (1 - P) * T * P = 0)
    (hcov : ∀ᵐ y ∂μ, p (σ y) = ↑(S⁻¹) * p y * (S : E →L[ℂ] E))
    {e : E} (he : ‖e‖ = 1) {f : Y → ℝ}
    (hD : ∀ᵐ y ∂μ, IsSelfAdjoint (D y))
    (hf : ∀ᵐ y ∂μ, f y ≠ 0)
    (heigen : ∀ᵐ y ∂μ, D y e = (f y : ℂ) • e)
    (hmean0 : 0 < (inner ℂ (Lp.const 2 μ e) (P (Lp.const 2 μ e))).re)
    (hmean1 : (inner ℂ (Lp.const 2 μ e) (P (Lp.const 2 μ e))).re < 1) :
    ∀ᵐ y ∂μ, 0 < (inner ℂ e (p y e)).re ∧ (inner ℂ e (p y e)).re < 1 := by
  have hproj := DirectIntegral.ae_isStarProjection_of_representation
    b P p C hC hbound hm hp hP
  have hfield := DirectIntegral.ae_invariant_of_represented_invariant
    b P T p (fun y => (S : E →L[ℂ] E) * D y) hp hT hinv
  have hreal := DirectIntegral.real_constant_vector_state_eq_integral P p hp e
  apply ae_strict_projection_diagonal_of_weighted_shift hσ S he hproj hD hf heigen
    hcov hfield
  · exact ((Complex.continuous_re.comp
      (continuous_const.inner continuous_id)).comp_stronglyMeasurable (hm e)).measurable
  · rwa [← hreal]
  · rwa [← hreal]

end Invariant233.Fields

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RealWeightedPositiveDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.PositiveDiagonalModel

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y}

theorem realWeightedShift_ae
    (a : Y → ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y k, |a y k| ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun y => a y k) μ)
    (ξ : Space μ) :
    realWeightedShift a C hC hbound hm ξ =ᵐ[μ] fun y =>
      (fiberShift * WeightedShift.diagonal (realWeight a C hbound y)) (ξ y) := by
  have hdiag := WeightedShift.fieldDiagonalVec_ae (realWeight a C hbound) C hC
    (fun y => lp.norm_le_of_forall_le hC (fun k => by
      simpa only [realWeight, Complex.norm_real, Real.norm_eq_abs] using hbound y k))
    (fun k => Complex.continuous_ofReal.comp_aestronglyMeasurable (hm k)) ξ
  filter_upwards [fiberShift.coeFn_compLpL (realDiagonal a C hC hbound hm ξ), hdiag]
    with y hs hd
  exact hs.trans (congrArg fiberShift hd)

omit [MeasurableSpace Y] in
theorem realWeight_diagonal_selfAdjoint
    (a : Y → ℤ → ℝ) (C : ℝ) (hbound : ∀ y k, |a y k| ≤ C) (y : Y) :
    IsSelfAdjoint (WeightedShift.diagonal (realWeight a C hbound y)) := by
  rw [isSelfAdjoint_iff, ← WeightedShift.diagonal_star]
  congr 1
  ext k
  simp [realWeight, lp.star_apply]

omit [MeasurableSpace Y] in
theorem realWeight_diagonal_e0
    (a : Y → ℤ → ℝ) (C : ℝ) (hbound : ∀ y k, |a y k| ≤ C) (y : Y) :
    WeightedShift.diagonal (realWeight a C hbound y) e0 = (a y 0 : ℂ) • e0 := by
  ext k
  change (a y k : ℂ) * (lp.single (E := fun _ : ℤ => ℂ) 2 0 1) k =
    (a y 0 : ℂ) * (lp.single (E := fun _ : ℤ => ℂ) 2 0 1) k
  by_cases hk : k = 0
  · subst k
    rfl
  · simp [lp.single_apply, hk]

theorem positive_diagonal
    [IsProbabilityMeasure μ] {σ : Y → Y} (hσ : Ergodic σ μ)
    (a : Y → ℤ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ y k, |a y k| ≤ C)
    (hm : ∀ k, AEStronglyMeasurable (fun y => a y k) μ)
    (hpositive : ∀ᵐ y ∂μ, 0 < a y 0)
    (P : Space μ →L[ℂ] Space μ) (p : Y → Fiber →L[ℂ] Fiber)
    (hpbound : ∀ y, ‖p y‖ ≤ ‖P‖)
    (hpm : ∀ v, StronglyMeasurable fun y => p y v)
    (hrep : ∀ ξ : Space μ, P ξ =ᵐ[μ] fun y => p y (ξ y))
    (hP : IsStarProjection P)
    (hcov : ∀ᵐ y ∂μ, p y * fiberShift = fiberShift * p (σ y))
    (hinv : (1 - P) * realWeightedShift a C hC hbound hm * P = 0)
    (htrace0 : 0 < diagonalState P) (htrace1 : diagonalState P < 1) :
    ∀ᵐ y ∂μ, 0 < (inner ℂ e0 (p y e0)).re ∧
      (inner ℂ e0 (p y e0)).re < 1 := by
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  apply Fields.ae_strict_diagonal_of_represented_weighted_shift b hσ P
    (realWeightedShift a C hC hbound hm) p
    (fun y => WeightedShift.diagonal (realWeight a C hbound y))
    fiberShiftUnit ‖P‖ (norm_nonneg P) hpbound hpm hrep
    (realWeightedShift_ae a C hC hbound hm) hP hinv
    ?_ norm_e0 (Eventually.of_forall (realWeight_diagonal_selfAdjoint a C hbound))
    (hpositive.mono fun _ hy => ne_of_gt hy)
    (Eventually.of_forall (realWeight_diagonal_e0 a C hbound)) htrace0 htrace1
  filter_upwards [hcov] with y hy
  have hh := congrArg (fun A : Fiber →L[ℂ] Fiber =>
    (↑(fiberShiftUnit⁻¹) : Fiber →L[ℂ] Fiber) * A) hy
  simpa only [← coe_fiberShiftUnit, ← mul_assoc, Units.inv_mul, one_mul] using hh.symm

end Invariant233.PositiveDiagonalModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductPositiveDiagonal
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.BlockedProductCoupling.circleLeftEndpoint_unflatten _root_.OAI.Invariant233.BlockedProductCoupling.circleRightEndpoint_unflatten _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.SamplingWeights.prefixWeight_restrict _root_.OAI.Invariant233.ProductModel.SamplingWeights.rectangle_univ _root_.OAI.Invariant233.ProductModel.TailTrimming.cylinderTestAverage_empty _root_.OAI.Invariant233.ProductModel.actualWeightField_apply _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.prefixPair_fst _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.ProductModel

theorem ae_strict_diagonal_of_invariant_projection
    {θ c : ℕ → ℝ} (hadm : AdmissibleAnglesAndCosts θ c)
    (P : Hilbert →L[ℂ] Hilbert) (hPm : P ∈ factor θ) (hP : IsStarProjection P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (hinv : (1 - P) * weightedOperator θ c * P = 0)
    (p : Base → Fiber →L[ℂ] Fiber)
    (hpbound : ∀ x, ‖p x‖ ≤ ‖P‖)
    (hpm : ∀ v, StronglyMeasurable fun x => p x v)
    (hrep : ∀ ξ : Hilbert, P ξ =ᵐ[baseMeasure] fun x => p x (ξ x)) :
    ∀ᵐ x ∂baseMeasure,
      0 < (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re ∧
      (inner ℂ PositiveDiagonalModel.e0 (p x PositiveDiagonalModel.e0)).re < 1 := by
  let a : Base → ℤ → ℝ := fun x k => weight θ c (rotationIterate θ k x)
  have hb : ∀ x k, |a x k| ≤ 1 := by
    intro x k
    rw [abs_of_nonneg (weight_mem_Icc θ c _).1]
    exact (weight_mem_Icc θ c _).2
  have hm : ∀ k, AEStronglyMeasurable (fun x => a x k) baseMeasure := by
    intro k
    exact ((measurable_weight θ c).comp
      (rotationIterate_measurePreserving θ k).measurable).aestronglyMeasurable
  have hT : weightedOperator θ c =
      PositiveDiagonalModel.realWeightedShift a 1 (by norm_num) hb hm := by
    rfl
  have hcov : ∀ᵐ x ∂baseMeasure,
      p x * PositiveDiagonalModel.fiberShift =
        PositiveDiagonalModel.fiberShift * p (rotationIterate θ 1 x) := by
    filter_upwards [field_covariance hPm p hrep] with x hx
    exact hx 1
  have hpos : ∀ᵐ x ∂baseMeasure, 0 < a x 0 := by
    simpa only [a, rotationIterate_zero] using
      ae_weight_pos θ c (fun i => (hadm.1 i).1.le)
        (fun i => (hadm.1 i).2.2.le) hadm.2.1
  have htrace := projection_vectorTrace_mem_Ioo hPm hP hP0 hP1
  apply PositiveDiagonalModel.positive_diagonal
    (rotationIterate_ergodic hadm.2.2 (by norm_num : (1 : ℤ) ≠ 0))
    a 1 (by norm_num) hb hm hpos P p hpbound hpm hrep hP hcov
  · rwa [← hT]
  · exact htrace.1
  · exact htrace.2

end Invariant233.ProductModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Product_ProductInvariantProjectionObstruction
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology InnerProductSpace

namespace Invariant233.ProductModel

theorem hasOnlyTrivialInvariantProjections_of_sampling_and_phases_oai
    {p : ProductScaleData} (hp : ProductScaleLaws p)
    (e : ℕ ≃ Σ s, Fin (p.m s))
    (he : ∀ a : Σ s, Fin (p.m s),
      e.symm a = (∑ r ∈ Finset.range a.1, p.m r) + a.2.val)
    (θ : ℕ → ℝ)
    (hadm : AdmissibleAnglesAndCosts θ (fun i => p.C (e i).1))
    (hb : ∀ j, ∀ i ∈ ProductPhases.consecutiveBlock p.m j,
      θ i ∈ Set.Icc (1 / p.N j) (2 / p.N j))
    (hsmall : ∀ s, ProductPhases.smallPhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.K s) (p.G s) θ)
    (hlarge : ∀ᶠ s in atTop, ProductPhases.largePhaseCondition
      (ProductPhases.consecutiveBlock p.m s) (p.N s) θ)
    (hsampling : HasAllFiniteCoordinateSampling θ) :
    HasOnlyTrivialInvariantProjections (factor θ)
      (weightedOperator θ (fun i => p.C (e i).1)) := by
  intro A hAm hA hinv
  by_cases hA0 : A = 0
  · exact Or.inl hA0
  by_cases hA1 : A = 1
  · exact Or.inr hA1
  exfalso
  have hθ0 : ∀ i, 0 ≤ θ i := fun i => (hadm.1 i).1.le
  have hc : ∀ i, 0 ≤ p.C (e i).1 := fun i => (hp.C_pos (e i).1).le
  obtain ⟨F, hF, hproj, htri⟩ := exists_covariantProjectionField_pairIdentity
    θ (fun i => p.C (e i).1) hθ0 hadm.2.1 hc hsampling A hAm hA hinv
  have hnorm : ‖A‖ = 1 := by
    have heq : ‖A‖ * ‖A‖ = ‖A‖ := by
      rw [← CStarRing.norm_star_mul_self, hA.isSelfAdjoint.star_eq,
        hA.isIdempotentElem.eq]
    have hpos : 0 < ‖A‖ := norm_pos_iff.mpr hA0
    nlinarith
  have hdiag := ae_strict_diagonal_of_invariant_projection hadm A hAm hA hA0 hA1
    hinv F (fun x => by simpa only [hnorm] using hF.2.1 x) hF.2.2.1 hF.2.2.2.1
  have hdiag' : ∀ᵐ x ∂baseMeasure,
      0 < BlockedProductCoupling.projectionDiagonal F x ∧
      BlockedProductCoupling.projectionDiagonal F x < 1 := by
    simpa only [BlockedProductCoupling.projectionDiagonal,
      BlockedProductCoupling.sourceBasisZero, PositiveDiagonalModel.e0,
      lp.inner_single_left, RCLike.inner_apply, map_one, mul_one] using hdiag
  have hpair := OrderedProductCoupling.source_circlePairLaw_pairIdentity_of_triangular
    p.m p.a p.b hp.m_ge_100
    (fun s => (hp.a_bounds s).1) (fun s => (hp.a_bounds s).2)
    (fun s => (hp.b_bounds s).1) (fun s => (hp.b_bounds s).2)
    e θ (fun i => p.C (e i).1) hθ0 hadm.2.1 hc F hproj
    (fun i => (hF.2.2.1 (lp.single 2 i 1)).measurable) htri
  have htail := hp.eventually_source_product_tail_estimate e he θ hθ0 hadm.2.1
    hb hsmall hlarge
  exact actualSource_projection_contradiction hp e he θ hθ0 hadm.2.1
    (fun i => hb (e i).1 i (ProductPhases.mem_consecutiveBlock_enumeration p.m e he i))
    A F hF hproj hinv hdiag' hpair htail

end Invariant233.ProductModel

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases_oai := @OAI.Invariant233.ProductModel.hasOnlyTrivialInvariantProjections_of_sampling_and_phases_oai
