-- Prove2me | solution 1 for OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:58.76438+00:00
-- url     : https://prove2.me/submissions/7e9177ba-c817-4f33-aca2-7e47cd9a9ff4

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
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
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
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
import Theorems.Thm_OAI_Invariant233_CircleCoupling_tendsto_centralBadEvent_mass
import Theorems.Thm_OAI_Invariant233_CircleParameterLaws_exists_rational_graph_field

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointIntervalBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace InvariantRotation.EndpointIntervalBounds

theorem withDensity_le_smul_of_ae_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {f : Ω → ℝ≥0∞} {C : ℝ≥0∞}
    (hf : ∀ᵐ x ∂μ, f x ≤ C) : μ.withDensity f ≤ C • μ := by
  rw [← withDensity_const]
  exact withDensity_mono hf

theorem measureReal_le_mul_of_le_smul {Ω : Type*} [MeasurableSpace Ω]
    {μ ν : Measure Ω} {C : ℝ} (hC : 0 ≤ C)
    (hdom : ν ≤ ENNReal.ofReal C • μ) (A : Set Ω) (hA : μ A ≠ ∞) :
    ν.real A ≤ C * μ.real A := by
  have hb : ν A ≤ ENNReal.ofReal C * μ A := by
    simpa only [Measure.smul_apply, smul_eq_mul] using hdom A
  have hfinite : ENNReal.ofReal C * μ A ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
  have hreal := ENNReal.toReal_mono hfinite hb
  simpa only [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using hreal

theorem intervalMeasure_lower_tail_le {d : ℝ} (hd : 0 ≤ d) :
    (volume.restrict (Ico (0 : ℝ) 1)).real (Iic d) ≤ d := by
  rw [measureReal_restrict_apply measurableSet_Iic]
  calc
    volume.real (Iic d ∩ Ico 0 1) ≤ volume.real (Icc 0 d) :=
      measureReal_mono (fun x hx => ⟨hx.2.1, hx.1⟩) (by simp)
    _ = d := by rw [Real.volume_real_Icc_of_le hd]; ring

theorem intervalMeasure_upper_tail_le {d : ℝ} (hd : 0 ≤ d) :
    (volume.restrict (Ico (0 : ℝ) 1)).real (Ici (1 - d)) ≤ d := by
  rw [measureReal_restrict_apply measurableSet_Ici]
  calc
    volume.real (Ici (1 - d) ∩ Ico 0 1) ≤ volume.real (Icc (1 - d) 1) :=
      measureReal_mono (fun x hx => ⟨hx.1, hx.2.2.le⟩) (by simp)
    _ = d := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring

theorem lower_endpoint_loss_le {ν : Measure ℝ} {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : ν ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    ν.real (Iic d) ≤ C * d := by
  refine (measureReal_le_mul_of_le_smul hC hdom (Iic d) ?_).trans
    (mul_le_mul_of_nonneg_left (intervalMeasure_lower_tail_le hd) hC)
  rw [Measure.restrict_apply measurableSet_Iic]
  exact (measure_mono (show Iic d ∩ Ico (0 : ℝ) 1 ⊆ Ico 0 1 from inter_subset_right)
    |>.trans_lt (by simp)).ne

theorem upper_endpoint_loss_le {ν : Measure ℝ} {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : ν ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    ν.real (Ici (1 - d)) ≤ C * d := by
  refine (measureReal_le_mul_of_le_smul hC hdom (Ici (1 - d)) ?_).trans
    (mul_le_mul_of_nonneg_left (intervalMeasure_upper_tail_le hd) hC)
  rw [Measure.restrict_apply measurableSet_Ici]
  exact (measure_mono inter_subset_right |>.trans_lt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).ne

theorem endpoint_function_lower_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | X ω ≤ d} ≤ C * d := by
  have h := lower_endpoint_loss_le hC hd hdom
  have heq : X ⁻¹' Iic d = {ω | X ω ≤ d} := by ext ω; simp
  simpa only [measureReal_def, Measure.map_apply hX measurableSet_Iic, heq] using h

theorem endpoint_function_upper_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdom : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | 1 - d ≤ X ω} ≤ C * d := by
  have h := upper_endpoint_loss_le hC hd hdom
  have heq : X ⁻¹' Ici (1 - d) = {ω | 1 - d ≤ X ω} := by ext ω; simp
  simpa only [measureReal_def, Measure.map_apply hX measurableSet_Ici, heq] using h

theorem endpoint_pair_loss_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {X Y : Ω → ℝ} (hX : Measurable X) (hY : Measurable Y)
    {C d : ℝ} (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hdomX : μ.map X ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : μ.map Y ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    μ.real {ω | 1 - d ≤ X ω ∨ Y ω ≤ d} ≤ 2 * C * d := by
  have hXb := endpoint_function_upper_loss_le μ hX hC hd hdomX
  have hYb := endpoint_function_lower_loss_le μ hY hC hd hdomY
  have h := (measureReal_union_le {ω | 1 - d ≤ X ω} {ω | Y ω ≤ d}).trans
    (add_le_add hXb hYb)
  have heq : {ω | 1 - d ≤ X ω} ∪ {ω | Y ω ≤ d} =
      {ω | 1 - d ≤ X ω ∨ Y ω ≤ d} := by ext ω; simp
  rw [heq] at h
  linarith

theorem measureReal_iUnion_le_tsum_budget {Ω ι : Type*}
    [MeasurableSpace Ω] [Countable ι] (μ : Measure Ω) [IsFiniteMeasure μ]
    (E : ι → Set Ω) {b : ι → ℝ} (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    (hE : ∀ i, μ.real (E i) ≤ b i) :
    μ.real (⋃ i, E i) ≤ ∑' i, b i := by
  have hE' : ∀ i, μ (E i) ≤ ENNReal.ofReal (b i) := by
    intro i
    rw [← ENNReal.ofReal_toReal (measure_ne_top μ (E i))]
    exact ENNReal.ofReal_le_ofReal (hE i)
  have hbound : μ (⋃ i, E i) ≤ ENNReal.ofReal (∑' i, b i) := calc
    _ ≤ ∑' i, μ (E i) := measure_iUnion_le E
    _ ≤ ∑' i, ENNReal.ofReal (b i) := ENNReal.tsum_le_tsum hE'
    _ = _ := (ENNReal.ofReal_tsum_of_nonneg hb hs).symm
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  simpa only [measureReal_def, ENNReal.toReal_ofReal (tsum_nonneg hb)] using hreal

end InvariantRotation.EndpointIntervalBounds

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_ParameterTails
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter
open scoped Topology

namespace Invariant233.ParameterTails

theorem tsum_tail_le_of_half_decay {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, a (n + 1) ≤ a n / 2) (j : ℕ) :
    (∑' n : ℕ, a (j + n)) ≤ 2 * a j := by
  have hs : Summable (fun n : ℕ => a (j + n)) :=
    summable_of_half_decay (fun n => ha (j + n))
      (fun n => by simpa only [Nat.add_assoc] using hstep (j + n))
  calc
    (∑' n : ℕ, a (j + n)) ≤ ∑' n : ℕ, a j * (1 / 2 : ℝ) ^ n :=
      hs.tsum_le_tsum (half_decay_iterate hstep j)
        (summable_geometric_two.mul_left (a j))
    _ = 2 * a j := by rw [tsum_mul_left, tsum_geometric_two]; ring

theorem reciprocal_tail_bound {K : ℕ → ℝ} (hK : ∀ n, 0 < K n)
    (hdouble : ∀ n, 2 * K n ≤ K (n + 1)) (j : ℕ) :
    (∑' n : ℕ, 1 / K (j + 1 + n)) ≤ 2 / K (j + 1) := by
  simpa only [div_eq_mul_inv, one_mul] using
    tsum_tail_le_of_half_decay (fun n => le_of_lt (one_div_pos.mpr (hK n)))
      (reciprocal_half_decay hK hdouble) (j + 1)

end Invariant233.ParameterTails

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_SamplingHorizon
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.SamplingHorizon

open Filter
open scoped Topology

theorem rpow_ratio_le_inv {x a b : ℝ} (hx : 1 ≤ x)
    (hgap : 1 ≤ (b - a) * x) :
    x ^ (a * x) / x ^ (b * x) ≤ x⁻¹ := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [← Real.rpow_sub hxpos, ← Real.rpow_neg_one]
  apply Real.rpow_le_rpow_of_exponent_le hx
  linarith

theorem horizon_ratio_le_inv {m K : ℝ} (hm : 20 ≤ m)
    (hK : m ^ ((3 / 4 : ℝ) * m) ≤ K) :
    m ^ ((7 / 10 : ℝ) * m) / K ≤ m⁻¹ := by
  have hmpos : 0 < m := by linarith
  have hpowpos : 0 < m ^ ((3 / 4 : ℝ) * m) := Real.rpow_pos_of_pos hmpos _
  calc
    m ^ ((7 / 10 : ℝ) * m) / K ≤
        m ^ ((7 / 10 : ℝ) * m) / m ^ ((3 / 4 : ℝ) * m) :=
      div_le_div_of_nonneg_left (Real.rpow_nonneg hmpos.le _) hpowpos hK
    _ ≤ m⁻¹ := rpow_ratio_le_inv (by linarith) (by linarith)

theorem tendsto_horizon_ratio {m K : ℕ → ℝ}
    (hm : Tendsto m atTop atTop)
    (hK : ∀ n, m n ^ ((3 / 4 : ℝ) * m n) ≤ K n) :
    Tendsto (fun n => m n ^ ((7 / 10 : ℝ) * m n) / K n) atTop (𝓝 0) := by
  have hlarge : ∀ᶠ n in atTop, 20 ≤ m n := hm.eventually_ge_atTop 20
  apply squeeze_zero' _ _ (tendsto_inv_atTop_zero.comp hm)
  · filter_upwards [hlarge] with n hn
    have hpos : 0 < m n := by linarith
    exact div_nonneg (Real.rpow_nonneg hpos.le _)
      (le_trans (Real.rpow_nonneg hpos.le _) (hK n))
  · filter_upwards [hlarge] with n hn
    exact horizon_ratio_le_inv hn (hK n)

theorem tendsto_horizon_ratio_of_pow_two_le {m K : ℕ → ℝ}
    (hm : ∀ n, (2 : ℝ) ^ n ≤ m n)
    (hK : ∀ n, m n ^ ((3 / 4 : ℝ) * m n) ≤ K (n + 1)) :
    Tendsto (fun n => m n ^ ((7 / 10 : ℝ) * m n) / K (n + 1))
      atTop (𝓝 0) := by
  apply tendsto_horizon_ratio _ hK
  exact tendsto_atTop_mono hm (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

end Invariant233.SamplingHorizon

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleParameterConsequences
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.CircleParameterData.blockEnd_zero _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

theorem reciprocal_tail_bound (j : ℕ) (hj : 1 ≤ j) :
    (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) ≤ 2 / (p.K (j + 1) : ℝ) := by
  have h := ParameterTails.reciprocal_tail_bound hp.shifted_K_pos hp.shifted_K_double (j - 1)
  simpa only [Nat.sub_add_cancel hj, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem tendsto_sampling_horizon :
    Tendsto (fun n : ℕ => p.Q (n + 1) / p.K (n + 2)) atTop (𝓝 0) := by
  apply SamplingHorizon.tendsto_horizon_ratio_of_pow_two_le
    (m := fun n => (p.m (n + 1) : ℝ)) (K := fun n => (p.K (n + 1) : ℝ))
  · intro n
    have hm : (2 : ℝ) ^ (n + 1) ≤ (p.m (n + 1) : ℝ) := by
      exact_mod_cast hp.m_ge_pow (n + 1) (by omega)
    have ht : (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith [pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n]
    exact ht.trans hm
  · intro n
    rw [hp.next_K (n + 1) (by omega)]
    exact Nat.le_ceil _

end CircleParameterLaws
end Invariant233

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

theorem fieldDiagonal_norm_map
    (hunit : ∀ᵐ x ∂μ, ∀ k, ‖a x k‖ = 1) (f : Lp Hilbert 2 μ) :
    ‖fieldDiagonal a C hC ha hm f‖ = ‖f‖ := by
  have hnorm : ∀ᵐ x ∂μ, ‖fieldDiagonal a C hC ha hm f x‖ = ‖f x‖ := by
    filter_upwards [fieldDiagonal_coordinate_ae a C hC ha hm f, hunit] with x hx hu
    have hcoord : ∀ k, ‖fieldDiagonal a C hC ha hm f x k‖ = ‖f x k‖ := by
      intro k
      rw [hx, norm_mul, hu, one_mul]
    exact le_antisymm (lp.norm_mono (by norm_num) fun k => (hcoord k).le)
      (lp.norm_mono (by norm_num) fun k => (hcoord k).symm.le)
  exact le_antisymm (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.le))
    (Lp.norm_le_norm_of_ae_le (hnorm.mono fun _ h => h.symm.le))

theorem fieldDiagonal_mem_unitary
    (hunit : ∀ᵐ x ∂μ, ∀ k, ‖a x k‖ = 1) :
    fieldDiagonal a C hC ha hm ∈ unitary (Lp Hilbert 2 μ →L[ℂ] Lp Hilbert 2 μ) := by
  have hb : ∀ x, ‖star (a x)‖ ≤ C := by simpa using ha
  have hn : ∀ k, AEStronglyMeasurable (fun x => star (a x) k) μ := by
    intro k
    simpa only [lp.coeFn_star, Pi.star_apply] using
      continuous_star.comp_aestronglyMeasurable (hm k)
  have hstar : fieldDiagonal (fun x => star (a x)) C hC hb hn =
      star (fieldDiagonal a C hC ha hm) :=
    fieldDiagonal_star_of_eq (Filter.Eventually.of_forall fun _ => rfl)
  have hunitstar : ∀ᵐ x ∂μ, ∀ k, ‖star (a x) k‖ = 1 := by
    simpa only [lp.coeFn_star, Pi.star_apply, norm_star] using hunit
  apply Unitary.mem_iff.mpr
  constructor
  · change ContinuousLinearMap.adjoint (fieldDiagonal a C hC ha hm) ∘L
      fieldDiagonal a C hC ha hm = 1
    exact ContinuousLinearMap.norm_map_iff_adjoint_comp_self _ |>.mp
      (fieldDiagonal_norm_map hunit)
  · have hh := ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (star (fieldDiagonal a C hC ha hm)) |>.mp (fun f => by
        rw [← hstar]
        exact fieldDiagonal_norm_map hunitstar f)
    change star (star (fieldDiagonal a C hC ha hm)) *
      star (fieldDiagonal a C hC ha hm) = 1 at hh
    simpa only [star_star] using hh

end Invariant233.WeightedShift

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_RepresentedFieldCommutation
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

theorem ae_covariance_of_represented_commute (b : HilbertBasis ι ℂ E)
    (T : Lp E 2 μ →L[ℂ] Lp E 2 μ) (F : X → E →L[ℂ] E)
    (S : E →L[ℂ] E) (σ : X → X) (hσ : MeasurePreserving σ μ μ)
    (hT : ∀ ξ : Lp E 2 μ, T ξ =ᵐ[μ] fun x => F x (ξ x))
    (hcomm : Commute T (shiftedPullback S σ hσ)) :
    ∀ᵐ x ∂μ, F x * S = S * F (σ x) := by
  apply Fields.ae_eq_of_countable_columns
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  intro i
  let ξ : Lp E 2 μ := Lp.const 2 μ (b i)
  let J := shiftedPullback S σ hσ
  have heq : T (J ξ) = J (T ξ) :=
    congrArg (fun A : Lp E 2 μ →L[ℂ] Lp E 2 μ => A ξ) hcomm.eq
  filter_upwards [hT (J ξ), FieldKoopman.operator_ae S σ hσ ξ,
    FieldKoopman.operator_ae S σ hσ (T ξ),
    hσ.quasiMeasurePreserving.ae (hT ξ),
    hσ.quasiMeasurePreserving.ae (Lp.coeFn_const 2 μ (b i))]
    with x hTJ hJ hJT hTσ hξ
  have hx := congrArg (fun η : Lp E 2 μ => η x) heq
  change ξ (σ x) = b i at hξ
  change T (J ξ) x = J (T ξ) x at hx
  rw [hTJ, hJ, hJT, hTσ, hξ] at hx
  exact hx

end Invariant233.DirectIntegral

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_Rotation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace Invariant233.Rotation

theorem orbitWeight_norm_le (θ : ℝ) (a : C(Circle, ℂ)) (x : Circle) :
    ‖orbitWeight θ a x‖ ≤ ‖a‖ :=
  lp.norm_le_of_forall_le (norm_nonneg a) (fun _ => a.norm_coe_le_norm _)

theorem action_one_ergodic {θ : ℝ} (hθ : Irrational θ) :
    Ergodic (action θ 1) circleMeasure := by
  change Ergodic (fun x : Circle => x + (1 : ℤ) • (θ : Circle)) circleMeasure
  simp only [one_zsmul]
  change Ergodic (fun x : Circle => x + (θ : Circle)) volume
  apply AddCircle.ergodic_add_right.mpr
  apply AddCircle.denseRange_zsmul_iff.mp
  apply AddCircle.denseRange_zsmul_coe_iff.mpr
  simpa using hθ

theorem U_mem_unitary : U ∈ unitary (Hilbert →L[ℂ] Hilbert) :=
  WeightedShift.fieldShift_mem_unitary 1

theorem V_mem_unitary (θ : ℝ) : V θ ∈ unitary (Hilbert →L[ℂ] Hilbert) := by
  unfold V representation
  apply WeightedShift.fieldDiagonal_mem_unitary
  exact Filter.Eventually.of_forall fun x k => character_norm (action θ k x)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationFields
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem commute_star_left_of_mem_unitary {A B : Hilbert →L[ℂ] Hilbert}
    (hA : A ∈ unitary (Hilbert →L[ℂ] Hilbert)) (hAB : Commute A B) :
    Commute (star A) B := by
  obtain ⟨h₁, h₂⟩ := Unitary.mem_iff.mp hA
  show star A * B = B * star A
  calc
    star A * B = star A * (B * (A * star A)) := by rw [h₂, mul_one]
    _ = star A * ((A * B) * star A) := by rw [← mul_assoc B A, ← hAB.eq]
    _ = (star A * A) * (B * star A) := by simp only [mul_assoc]
    _ = B * star A := by rw [h₁, one_mul]

theorem U_commutes_multiplier (g : Lp ℂ ∞ circleMeasure) :
    Commute U (L2Multiplication.multiplier (E := Fiber) g) := by
  show U * L2Multiplication.multiplier g = L2Multiplication.multiplier g * U
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [U_coordinates_ae (L2Multiplication.multiplier g ξ),
    L2Multiplication.multiplier_coe g ξ, L2Multiplication.multiplier_coe g (U ξ),
    U_coordinates_ae ξ] with x hU hM hMU hUξ
  intro k
  change U (L2Multiplication.multiplier g ξ) x k =
    L2Multiplication.multiplier g (U ξ) x k
  rw [hU k, hM, hMU]
  change g x * ξ x (k - 1) = g x * U ξ x k
  rw [hUξ k]

theorem representation_commutes_multiplier (θ : ℝ) (a : C(Circle, ℂ))
    (g : Lp ℂ ∞ circleMeasure) :
    Commute (representation θ a) (L2Multiplication.multiplier (E := Fiber) g) := by
  show representation θ a * L2Multiplication.multiplier g =
    L2Multiplication.multiplier g * representation θ a
  apply operator_ext_of_coordinates
  intro ξ
  filter_upwards [representation_coordinates_ae θ a (L2Multiplication.multiplier g ξ),
    L2Multiplication.multiplier_coe g ξ,
    L2Multiplication.multiplier_coe g (representation θ a ξ),
    representation_coordinates_ae θ a ξ] with x ha hM hMa haξ
  intro k
  change representation θ a (L2Multiplication.multiplier g ξ) x k =
    L2Multiplication.multiplier g (representation θ a ξ) x k
  rw [ha k, hM, hMa]
  change a (action θ k x) * (g x * ξ x k) =
    g x * representation θ a ξ x k
  rw [haξ k]
  ring

theorem multiplier_mem_commutant (θ : ℝ) (g : Lp ℂ ∞ circleMeasure) :
    L2Multiplication.multiplier (E := Fiber) g ∈ (algebra θ).commutant := by
  apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
  intro A hA
  rcases Set.mem_insert_iff.mp hA with rfl | hA
  · exact ⟨(U_commutes_multiplier g).eq,
      (commute_star_left_of_mem_unitary U_mem_unitary (U_commutes_multiplier g)).eq⟩
  · have hAV : A = V θ := Set.mem_singleton_iff.mp hA
    subst A
    have hcomm := representation_commutes_multiplier θ character g
    exact ⟨hcomm.eq,
      (commute_star_left_of_mem_unitary (V_mem_unitary θ) hcomm).eq⟩

theorem algebra_commutes_multiplier (θ : ℝ) {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) (g : Lp ℂ ∞ circleMeasure) :
    Commute T (L2Multiplication.multiplier (E := Fiber) g) := by
  exact (VonNeumannAlgebra.mem_commutant_iff.mp (multiplier_mem_commutant θ g)) T hT

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationFieldRepresentation
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.Rotation

theorem exists_unique_field {θ : ℝ} {T : Hilbert →L[ℂ] Hilbert}
    (hT : T ∈ algebra θ) :
    ∃ F : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, ‖F x‖ ≤ ‖T‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      (∀ G : Circle → Fiber →L[ℂ] Fiber,
        (∀ ξ : Hilbert, T ξ =ᵐ[circleMeasure] fun x => G x (ξ x)) →
          F =ᵐ[circleMeasure] G) :=
  L2Multiplication.exists_unique_field_of_commutes
    (default : HilbertBasis ℤ ℂ Fiber) T (algebra_commutes_multiplier θ hT)

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationCenter
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter

namespace Invariant233.Rotation

theorem algebra_commutes_shiftedPullback_int_independent (θ : ℝ) (m : ℤ)
    {T : Hilbert →L[ℂ] Hilbert} (hT : T ∈ algebra θ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift m).toLinearIsometry.toContinuousLinearMap
      (action θ m) (action_measurePreserving θ m)) := by
  apply FieldKoopman.commute_of_mem_generated_of_unitary
    ({U, V θ} : Set (Hilbert →L[ℂ] Hilbert))
    (FieldKoopman.operator_mem_unitary (WeightedShift.shift m)
      (action θ m) (action θ (-m))
      (action_measurePreserving θ m) (action_measurePreserving θ (-m))
      (by funext x; simp)
      (by funext x; simp)) _ hT
  intro B hB
  rcases Set.mem_insert_iff.mp hB with rfl | hB
  · exact FieldKoopman.commute_fieldShifts 1 m (action θ m)
      (action_measurePreserving θ m)
  · have hB' : B = V θ := Set.mem_singleton_iff.mp hB
    subst B
    apply FieldKoopman.commute_fieldDiagonal
      (orbitWeight θ character) ‖character‖ (norm_nonneg character)
      (fun x => orbitWeight_norm_le θ character x)
      (fun k => (character.continuous.comp (action_continuous θ k)).aestronglyMeasurable)
      m (action θ m) (action_measurePreserving θ m)
    exact Filter.Eventually.of_forall fun x k => by
      simp only [orbitWeight_apply, action_add, sub_add_cancel]

end Invariant233.Rotation

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TaggedEventBounds
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantRotation.TaggedEventBounds

theorem neg_div_one_sub_le_log {t : ℝ} (ht : t < 1) :
    -t / (1 - t) ≤ Real.log (1 - t) := by
  have hp : 0 < 1 - t := sub_pos.mpr ht
  have heq : -t / (1 - t) = 1 - (1 - t)⁻¹ := by
    field_simp
    ring
  rw [heq]
  exact Real.one_sub_inv_le_log_of_pos hp

theorem exp_neg_le_one_sub_pow (n : ℕ) {t a : ℝ} (ht : t < 1)
    (hbudget : (n : ℝ) * t ≤ a * (1 - t)) :
    Real.exp (-a) ≤ (1 - t) ^ n := by
  have hp : 0 < 1 - t := sub_pos.mpr ht
  apply (Real.le_log_iff_exp_le (pow_pos hp n)).mp
  rw [Real.log_pow]
  have hb : -a ≤ (n : ℝ) * (-t / (1 - t)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hp).mpr
    nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left
    (neg_div_one_sub_le_log ht) (Nat.cast_nonneg n))

theorem circle_tag_bound (m : ℕ) (hm : 200 ≤ m) :
    Real.exp (-90) ≤ (1 - 61 / (m : ℝ)) ^ (m - 1) := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < m := by linarith
  have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  apply exp_neg_le_one_sub_pow (m - 1)
  · exact (div_lt_one hmpos).mpr (by linarith)
  · rw [hsub]
    apply (mul_le_mul_iff_left₀ hmpos).mp
    field_simp
    nlinarith

open MeasureTheory

section ProductEvent

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

omit [Fintype ι] [MeasurableSpace Ω] in
theorem tagRectangle_pairwiseDisjoint (T G : ι → Set Ω)
    (hdis : ∀ i, Disjoint (T i) (G i)) :
    Pairwise (fun i j => Disjoint (tagRectangle T G i) (tagRectangle T G j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have hi : x i ∈ T i := by simpa [tagRectangle] using hxi i (Set.mem_univ i)
  have hj : x i ∈ G i := by simpa [tagRectangle, hij] using hxj i (Set.mem_univ i)
  exact Set.disjoint_left.mp (hdis i) hi hj

theorem measurableSet_tagRectangle (T G : ι → Set Ω)
    (hT : ∀ i, MeasurableSet (T i)) (hG : ∀ i, MeasurableSet (G i)) (i : ι) :
    MeasurableSet (tagRectangle T G i) := by
  apply MeasurableSet.univ_pi
  intro j
  split_ifs
  · exact hT j
  · exact hG j

theorem oneTagEvent_measureReal (μ : ι → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : ι → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i)) :
    (Measure.pi μ).real (oneTagEvent T G) =
      ∑ i, ∏ j, (μ j).real (if j = i then T j else G j) := by
  rw [oneTagEvent, measureReal_iUnion_fintype (tagRectangle_pairwiseDisjoint T G hdis)
    (measurableSet_tagRectangle T G hT hG)]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [tagRectangle, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]

theorem oneTagEvent_measureReal_lower_bound
    (μ : ι → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : ι → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    {t g : ℝ} (ht : 0 ≤ t) (hg : 0 ≤ g)
    (hTag : ∀ i, t ≤ (μ i).real (T i)) (hGood : ∀ i, g ≤ (μ i).real (G i)) :
    (Fintype.card ι : ℝ) * t * g ^ (Fintype.card ι - 1) ≤
      (Measure.pi μ).real (oneTagEvent T G) := by
  rw [oneTagEvent_measureReal μ T G hT hG hdis]
  have hprod (i : ι) : (∏ j : ι, if j = i then t else g) =
      t * g ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun j => if j = i then t else g) (Finset.mem_univ i)]
    simp only [ite_true, if_true]
    congr 1
    calc
      (∏ j ∈ Finset.univ.erase i, if j = i then t else g) =
          ∏ _j ∈ Finset.univ.erase i, g := by
        apply Finset.prod_congr rfl
        intro j hj
        exact ite_eq_right (Finset.mem_erase.mp hj).1
      _ = g ^ (Fintype.card ι - 1) := by simp
  calc
    (Fintype.card ι : ℝ) * t * g ^ (Fintype.card ι - 1) =
        ∑ _i : ι, t * g ^ (Fintype.card ι - 1) := by simp [mul_assoc]
    _ = ∑ i : ι, ∏ j : ι, if j = i then t else g := by simp_rw [hprod]
    _ ≤ ∑ i, ∏ j, (μ j).real (if j = i then T j else G j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.prod_le_prod
      · intro j hj
        split_ifs <;> assumption
      · intro j hj
        split_ifs
        · exact hTag j
        · exact hGood j

theorem oneTagEvent_measureReal_ge_pow (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsFiniteMeasure (μ i)]
    (T G : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hG : ∀ i, MeasurableSet (G i)) (hdis : ∀ i, Disjoint (T i) (G i))
    {g : ℝ} (hg : 0 ≤ g)
    (hTag : ∀ i, 1 / (m : ℝ) ≤ (μ i).real (T i))
    (hGood : ∀ i, g ≤ (μ i).real (G i)) :
    g ^ (m - 1) ≤ (Measure.pi μ).real (oneTagEvent T G) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := oneTagEvent_measureReal_lower_bound μ T G hT hG hdis
    (t := 1 / (m : ℝ)) (by positivity) hg hTag hGood
  simp only [Fintype.card_fin] at h
  have hcancel : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
  simpa only [hcancel, one_mul] using h

end ProductEvent

section EventLoss

variable {Ω : Type*} [MeasurableSpace Ω]

theorem admissible_nontag_measureReal_lower_bound
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T B₁ B₂ : Set Ω)
    (hT : MeasurableSet T) (hB₁ : MeasurableSet B₁) (hB₂ : MeasurableSet B₂)
    {t b₁ b₂ : ℝ} (hTag : μ.real T ≤ t)
    (hBad₁ : μ.real B₁ ≤ b₁) (hBad₂ : μ.real B₂ ≤ b₂) :
    1 - t - b₁ - b₂ ≤ μ.real (Tᶜ ∩ B₁ᶜ ∩ B₂ᶜ) := by
  have hbound : μ.real (T ∪ B₁ ∪ B₂) ≤ t + b₁ + b₂ :=
    (measureReal_union_le (T ∪ B₁) B₂).trans
      (add_le_add ((measureReal_union_le T B₁).trans (add_le_add hTag hBad₁)) hBad₂)
  have heq : μ.real (Tᶜ ∩ B₁ᶜ ∩ B₂ᶜ) = 1 - μ.real (T ∪ B₁ ∪ B₂) := by
    rw [← Set.compl_union, ← Set.compl_union, measureReal_compl (hT.union hB₁ |>.union hB₂)]
    simp
  rw [heq]
  linarith

end EventLoss


variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

omit [Fintype ι] [MeasurableSpace Ω] in
theorem oneTagEvent_subset_currentBlockEvent (T B₁ B₂ : ι → Set Ω)
    (hTagSafe : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) :
    oneTagEvent T (fun i => (T i)ᶜ ∩ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) ⊆
      currentBlockEvent T B₁ B₂ := by
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have htag : x i ∈ T i := by
    simpa [tagRectangle] using hi i (Set.mem_univ i)
  refine ⟨⟨i, htag⟩, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    exact hTagSafe i htag
  · have hj : x j ∈ (T j)ᶜ ∩ (B₁ j)ᶜ ∩ (B₂ j)ᶜ := by
      simpa [tagRectangle, hji] using hi j (Set.mem_univ j)
    exact ⟨hj.1.2, hj.2⟩

theorem currentBlockEvent_measureReal_lower_bound (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T B₁ B₂ : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    (hB₁ : ∀ i, MeasurableSet (B₁ i)) (hB₂ : ∀ i, MeasurableSet (B₂ i))
    (hTagSafe : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ) {a : ℝ}
    (hg : 0 ≤ 1 - (1 + 2 * a) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hBad₁ : ∀ i, (μ i).real (B₁ i) ≤ a / (m : ℝ))
    (hBad₂ : ∀ i, (μ i).real (B₂ i) ≤ a / (m : ℝ)) :
    (1 - (1 + 2 * a) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real (currentBlockEvent T B₁ B₂) := by
  let G : Fin m → Set Ω := fun i => (T i)ᶜ ∩ (B₁ i)ᶜ ∩ (B₂ i)ᶜ
  have hG : ∀ i, MeasurableSet (G i) := fun i =>
    ((hT i).compl.inter (hB₁ i).compl).inter (hB₂ i).compl
  have hdis : ∀ i, Disjoint (T i) (G i) := by
    intro i
    exact Set.disjoint_left.mpr (fun x hx hGx => hGx.1.1 hx)
  have hGood : ∀ i, 1 - (1 + 2 * a) / (m : ℝ) ≤ (μ i).real (G i) := by
    intro i
    have h := admissible_nontag_measureReal_lower_bound (μ i) (T i) (B₁ i) (B₂ i)
      (hT i) (hB₁ i) (hB₂ i) (le_of_eq (hTag i)) (hBad₁ i) (hBad₂ i)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    ring
  exact (oneTagEvent_measureReal_ge_pow m hm μ T G hT hG hdis hg
    (fun i => (hTag i).ge) hGood).trans
    (measureReal_mono (oneTagEvent_subset_currentBlockEvent T B₁ B₂ hTagSafe))


end InvariantRotation.TaggedEventBounds

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_TruncationEvent
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal

namespace InvariantRotation.TruncationEvent

open TaggedEventBounds EndpointIntervalBounds

variable {Ω : Type*} [MeasurableSpace Ω]

theorem currentBlock_mass_lower_bound (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    {X Y : Fin m → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbudget : 0 ≤ 1 - (1 + 2 * (C * a)) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hSafe : ∀ i, ∀ x ∈ T i, X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x)
    (hdomX : ∀ i, (μ i).map (X i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, (μ i).map (Y i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    (1 - (1 + 2 * (C * a)) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real {x | (∃ i, x i ∈ T i) ∧
        ∀ i, X i (x i) < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i (x i)} := by
  let B₁ : Fin m → Set Ω := fun i => {x | 1 - a / (m : ℝ) ≤ X i x}
  let B₂ : Fin m → Set Ω := fun i => {x | Y i x ≤ a / (m : ℝ)}
  have hB₁ : ∀ i, MeasurableSet (B₁ i) := fun i =>
    measurableSet_le measurable_const (hX i)
  have hB₂ : ∀ i, MeasurableSet (B₂ i) := fun i =>
    measurableSet_le (hY i) measurable_const
  have hSafe' : ∀ i, T i ⊆ (B₁ i)ᶜ ∩ (B₂ i)ᶜ := by
    intro i x hx
    exact ⟨not_le.mpr (hSafe i x hx).1, not_le.mpr (hSafe i x hx).2⟩
  have hd : 0 ≤ a / (m : ℝ) := div_nonneg ha (Nat.cast_nonneg m)
  have hBad₁ : ∀ i, (μ i).real (B₁ i) ≤ C * a / (m : ℝ) := by
    intro i
    simpa only [mul_div_assoc] using endpoint_function_upper_loss_le
      (μ i) (hX i) hC hd (hdomX i)
  have hBad₂ : ∀ i, (μ i).real (B₂ i) ≤ C * a / (m : ℝ) := by
    intro i
    simpa only [mul_div_assoc] using endpoint_function_lower_loss_le
      (μ i) (hY i) hC hd (hdomY i)
  have h := currentBlockEvent_measureReal_lower_bound m hm μ T B₁ B₂ hT hB₁ hB₂
    hSafe' hbudget hTag hBad₁ hBad₂
  simpa only [currentBlockEvent, B₁, B₂, Set.mem_ofPred_eq, not_le] using h

theorem currentBlock_mass_lower_bound_ae (m : ℕ) (hm : 0 < m)
    (μ : Fin m → Measure Ω) [∀ i, IsProbabilityMeasure (μ i)]
    (T : Fin m → Set Ω) (hT : ∀ i, MeasurableSet (T i))
    {X Y : Fin m → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (hbudget : 0 ≤ 1 - (1 + 2 * (C * a)) / (m : ℝ))
    (hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ))
    (hSafe : ∀ i, ∀ᵐ x ∂μ i, x ∈ T i →
      X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x)
    (hdomX : ∀ i, (μ i).map (X i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1))
    (hdomY : ∀ i, (μ i).map (Y i) ≤ ENNReal.ofReal C • volume.restrict (Ico (0 : ℝ) 1)) :
    (1 - (1 + 2 * (C * a)) / (m : ℝ)) ^ (m - 1) ≤
      (Measure.pi μ).real {x | (∃ i, x i ∈ T i) ∧
        ∀ i, X i (x i) < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i (x i)} := by
  let T' : Fin m → Set Ω := fun i => T i ∩
    {x | X i x < 1 - a / (m : ℝ) ∧ a / (m : ℝ) < Y i x}
  have hT' : ∀ i, MeasurableSet (T' i) := fun i =>
    (hT i).inter ((measurableSet_lt (hX i) measurable_const).inter
      (measurableSet_lt measurable_const (hY i)))
  have hTag' : ∀ i, (μ i).real (T' i) = 1 / (m : ℝ) := by
    intro i
    have hae : T' i =ᵐ[μ i] T i := by
      filter_upwards [hSafe i] with x hx
      exact propext ⟨fun h => h.1, fun h => ⟨h, hx h⟩⟩
    exact (measureReal_congr hae).trans (hTag i)
  have h := currentBlock_mass_lower_bound m hm μ T' hT' hX hY hC ha hbudget hTag'
    (fun i x hx => hx.2) hdomX hdomY
  refine h.trans (measureReal_mono ?_)
  intro x hx
  obtain ⟨⟨i, hi⟩, hgood⟩ := hx
  exact ⟨⟨i, hi.1⟩, hgood⟩

end InvariantRotation.TruncationEvent

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

lemma diagonal_fst (μ : Measure X) : (diagonal μ).fst = μ := by
  simpa [diagonal] using
    (Measure.fst_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma diagonal_snd (μ : Measure X) : (diagonal μ).snd = μ := by
  simpa [diagonal] using
    (Measure.snd_map_prodMk (μ := μ) (X := id) (Y := id) measurable_id)

lemma fst_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).fst = ∑ i ∈ s, (μ i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma snd_finsetSum {J : Type*} (s : Finset J) (μ : J → Measure (X × X)) :
    (∑ i ∈ s, μ i).snd = ∑ i ∈ s, (μ i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [Finset.sum_insert ha, ih]

lemma mixture_fst (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).fst = q • μ + ∑ i, p i • u i := by
  unfold mixture
  rw [Measure.fst_add, fst_finsetSum]
  simp only [Measure.fst, Measure.map_smul,
    Measure.map_fst_prod, measure_univ, one_smul]
  rw [← Measure.fst, diagonal_fst]

lemma mixture_snd (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] :
    (mixture μ q p u v).snd = q • μ + ∑ i, p i • v i := by
  unfold mixture
  rw [Measure.snd_add, snd_finsetSum]
  simp only [Measure.snd, Measure.map_smul,
    Measure.map_snd_prod, measure_univ, one_smul]
  rw [← Measure.snd, diagonal_snd]

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

omit [Fintype I] in
lemma map_label_event [DecidableEq I] [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (ν : Measure (X × X)) (l j : Option I) :
    ν.map (fun z => (l, z)) {z | z.1 = j} = if l = j then ν Set.univ else 0 := by
  classical
  have hs : MeasurableSet {z : Option I × (X × X) | z.1 = j} :=
    measurable_fst (measurableSet_singleton j)
  rw [Measure.map_apply (show Measurable (fun z : X × X => (l, z)) from
    measurable_const.prodMk measurable_id) hs]
  by_cases h : l = j <;> simp [h]

lemma labelledMixture_some_mass [MeasurableSpace (Option I)] [MeasurableSingletonClass (Option I)]
    (μ : Measure X) (q : ℝ≥0∞) (p : I → ℝ≥0∞)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)] (i : I) :
    labelledMixture μ q p u v {z | z.1 = some i} = p i := by
  classical
  simp only [labelledMixture, Measure.add_apply, Measure.smul_apply,
    Measure.finsetSum_apply, smul_eq_mul, map_label_event]
  simp

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

lemma mixture_fst_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hu : ∀ i, u i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).fst =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_fst]
  simp_rw [hu, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

lemma mixture_snd_real_density (μ : Measure X) (q : ℝ) (p : I → ℝ)
    (u v : I → Measure X) [∀ i, IsProbabilityMeasure (u i)]
    [∀ i, IsProbabilityMeasure (v i)]
    (g : I → X → ℝ) (hq : 0 ≤ q) (hp : ∀ i, 0 ≤ p i)
    (hg0 : ∀ i x, 0 ≤ g i x) (hgm : ∀ i, Measurable (g i))
    (hv : ∀ i, v i = μ.withDensity (fun x => ENNReal.ofReal (g i x))) :
    (mixture μ (ENNReal.ofReal q) (fun i => ENNReal.ofReal (p i)) u v).snd =
      μ.withDensity (fun x => ENNReal.ofReal (q + ∑ i, p i * g i x)) := by
  rw [mixture_snd]
  simp_rw [hv, ofReal_mixture_density q p g hq hp hg0]
  exact (withDensity_finite_mixture μ _ _ _ (fun i => (hgm i).ennreal_ofReal)).symm

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
-- module Solutions.Q234_IR.IrrationalRotation_Operators_FaithfulProjectionTrace
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.IsFaithfulTracialVector.toTracialState_apply _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProjectionMeetTrace.vectorFunctional_apply _root_.OAI.Invariant233.vectorTraceCLM_apply _root_.OAI.Invariant233.vectorTraceContinuousLinearMap_apply _root_.OAI.Invariant233.vonNeumannVectorTraceCLM_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped InnerProductSpace

namespace Invariant233

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

theorem strict_positive_trace_of_nonzero_projection
    (M : VonNeumannAlgebra H) (ξ : H) (htrace : IsFaithfulTracialVector M ξ)
    (P : H →L[ℂ] H) (hPm : P ∈ M) (hP : IsStarProjection P) (hP0 : P ≠ 0) :
    0 < (vectorTrace ξ P).re := by
  have hnonneg := (InvariantProjection.projection_re_inner_bounds hP ξ).1
  apply lt_of_le_of_ne hnonneg
  intro heq
  have hzero : P ξ = 0 :=
    (InvariantProjection.projection_re_inner_eq_zero_iff hP ξ).mp heq.symm
  apply hP0
  exact htrace.2.2 P hPm (ContinuousLinearMap.IsPositive.of_isStarProjection hP)
    (by simp only [vectorTrace, hzero, inner_zero_right])

theorem strict_trace_bounds_of_nontrivial_projection
    (M : VonNeumannAlgebra H) (ξ : H) (htrace : IsFaithfulTracialVector M ξ)
    (P : H →L[ℂ] H) (hPm : P ∈ M) (hP : IsStarProjection P)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    0 < (vectorTrace ξ P).re ∧ (vectorTrace ξ P).re < 1 := by
  refine ⟨strict_positive_trace_of_nonzero_projection M ξ htrace P hPm hP hP0, ?_⟩
  have hcomp := strict_positive_trace_of_nonzero_projection M ξ htrace
    (1 - P) (M.sub_mem M.one_mem hPm) hP.one_sub
    (sub_ne_zero.mpr (Ne.symm hP1))
  have hself : (inner ℂ ξ ξ).re = 1 := by
    calc
      (inner ℂ ξ ξ).re = ‖ξ‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) ξ
      _ = 1 := by rw [htrace.1]; norm_num
  simp only [vectorTrace, sub_apply,
    one_apply_eq_self, inner_sub_right, Complex.sub_re,
    hself] at hcomp ⊢
  exact sub_pos.mp hcomp

end Invariant233

end

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

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRawTagEvent
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

section Parameters
variable {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1)
include hκ0 hκ hm ha ha' hb hb' ht0 ht

lemma rawLaw_map_endpoint_density (side : Bool) :
    (rawLaw κ m a b t).map (endpoint side) = baseLaw.withDensity
      (fun x => ENNReal.ofReal (marginalDensity side κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have hm2 : 2 ≤ 2 * m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure hm2 ha0 ha' hb0 hb'
  have hq : 0 ≤ diagonalMass κ m a b t :=
    le_trans (by norm_num) (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have hp := componentProbabilities_nonneg (a := a) (b := b) hκ0 hm0 ht0
  cases side
  · change ((labelledMixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
      (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
      (leftLaw (2 * m) a b) (rightLaw (2 * m) a b)).map
      (Prod.fst ∘ Prod.snd)) = _
    rw [← Measure.map_map measurable_fst measurable_snd, labelledMixture_map_snd]
    exact mixture_fst_real_density baseLaw _ _ _ _
      (fun i => leftDensity (2 * m) a b i) hq hp
      (fun i x => (leftDensity_bound hm2 ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (leftLaw_eq_withDensity hm2 ha0 ha' hb0 hb')
  · change ((labelledMixture baseLaw (ENNReal.ofReal (diagonalMass κ m a b t))
      (fun i => ENNReal.ofReal (componentProbabilities κ m a b t i))
      (leftLaw (2 * m) a b) (rightLaw (2 * m) a b)).map
      (Prod.snd ∘ Prod.snd)) = _
    rw [← Measure.map_map measurable_snd measurable_snd, labelledMixture_map_snd]
    exact mixture_snd_real_density baseLaw _ _ _ _
      (fun i => rightDensity (2 * m) a b i) hq hp
      (fun i x => (rightDensity_bound hm2 ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (rightLaw_eq_withDensity hm2 ha0 ha' hb0 hb')

lemma rawLaw_map_endpoint_le_ten (side : Bool) :
    (rawLaw κ m a b t).map (endpoint side) ≤ (10 : ℝ≥0∞) • baseLaw := by
  rw [rawLaw_map_endpoint_density hκ0 hκ hm ha ha' hb hb' ht0 ht]
  calc
    _ ≤ baseLaw.withDensity (fun _ => (10 : ℝ≥0∞)) := by
      apply withDensity_mono
      exact Filter.Eventually.of_forall (fun x => by
        exact le_trans (ENNReal.ofReal_le_ofReal
          (marginalDensity_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht side x).2.2.le)
          (by norm_num))
    _ = _ := withDensity_const _

end Parameters

lemma rawLaw_tag_mass {κ m a b t : ℝ} (hm : 1 ≤ m)
    (ha0 : 0 < a) (ha1 : a ≤ 1 / 4) (hb0 : 0 < b) (hb1 : b ≤ 1 / 4) :
    rawLaw κ m a b t {z | z.1 = some (4 : Fin 5)} = ENNReal.ofReal (t / m) := by
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha1 hb0 hb1
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha1 hb0 hb1
  exact labelledMixture_some_mass _ _ _ _ _ (4 : Fin 5)

theorem rawLaw_ae_tag_interval (κ m a b t : ℝ) :
    ∀ᵐ z ∂rawLaw κ m a b t, z.1 = some (4 : Fin 5) →
      z.2.1 < 1 / (2 * m) ∧ 1 - 1 / (2 * m) ≤ z.2.2 := by
  let P : Option (Fin 5) × (ℝ × ℝ) → Prop := fun z =>
    z.1 = some (4 : Fin 5) → z.2.1 < 1 / (2 * m) ∧ 1 - 1 / (2 * m) ≤ z.2.2
  have hP : MeasurableSet {z | P z} := by
    simp only [P, imp_iff_not_or]
    change MeasurableSet ({z : Option (Fin 5) × (ℝ × ℝ) | z.1 = some (4 : Fin 5)}ᶜ ∪
      {z : Option (Fin 5) × (ℝ × ℝ) | z.2.1 < 1 / (2 * m) ∧ 1 - 1 / (2 * m) ≤ z.2.2})
    exact (measurable_fst (measurableSet_singleton _)).compl.union
      ((measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).inter
       (measurableSet_le measurable_const (measurable_snd.comp measurable_snd)))
  change ∀ᵐ z ∂rawLaw κ m a b t, P z
  rw [rawLaw, labelledMixture, ae_add_measure_iff, ae_finsetSum_measure_iff]
  constructor
  · apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    exact Filter.Eventually.of_forall (by intro z; simp [P])
  · intro i _
    apply Measure.ae_smul_measure
    apply (ae_map_iff (measurable_const.prodMk measurable_id).aemeasurable hP).2
    by_cases hi : i = 4
    · subst i
      change ∀ᵐ z ∂(intervalLaw 0 (1 / (2 * m))).prod (intervalLaw (1 - 1 / (2 * m)) 1),
        P (some 4, z)
      have : IsZeroOrProbabilityMeasure (intervalLaw 0 (1 / (2 * m))) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico 0 (1 / (2 * m))]))
      have : IsZeroOrProbabilityMeasure (intervalLaw (1 - 1 / (2 * m)) 1) := inferInstanceAs
        (IsZeroOrProbabilityMeasure (volume[|Ico (1 - 1 / (2 * m)) 1]))
      have hs : MeasurableSet {z : ℝ × ℝ | P (some 4, z)} :=
        hP.preimage (measurable_const.prodMk measurable_id)
      rw [Measure.ae_prod_iff_ae_ae hs]
      filter_upwards [intervalLaw_ae_mem 0 (1 / (2 * m))] with x hx
      filter_upwards [intervalLaw_ae_mem (1 - 1 / (2 * m)) 1] with y hy
      exact fun _ => ⟨hx.2, hy.1⟩
    · exact Filter.Eventually.of_forall (by intro z; simp [P, hi])

theorem concrete_circle_currentBlock_mass (m : ℕ) (hm : 200 ≤ m)
    (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100)
    (a b : Fin m → ℝ)
    (ha : ∀ i, 1 / (m : ℝ) ≤ a i) (ha' : ∀ i, a i ≤ 1 / 4)
    (hb : ∀ i, 1 / (m : ℝ) ≤ b i) (hb' : ∀ i, b i ≤ 1 / 4) :
    Real.exp (-90) ≤
      (Measure.pi (fun i => rawLaw κ m (a i) (b i) 1)).real
        {z | (∃ i, (z i).1 = some (4 : Fin 5)) ∧
          ∀ i, (z i).2.1 < 1 - 3 / (m : ℝ) ∧ 3 / (m : ℝ) < (z i).2.2} := by
  have hmR : (200 : ℝ) ≤ m := by exact_mod_cast hm
  have hm100 : (100 : ℝ) ≤ m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith
  let μ := fun i : Fin m => rawLaw κ m (a i) (b i) 1
  have : ∀ i, IsProbabilityMeasure (μ i) := fun i =>
    rawLaw_isProbabilityMeasure hκ0 hκ hm100 (ha i) (ha' i) (hb i) (hb' i)
      (by norm_num) (by norm_num)
  let T : Fin m → Set CoordinateSample := fun _ => {z | z.1 = some (4 : Fin 5)}
  have hT : ∀ i, MeasurableSet (T i) := fun _ =>
    measurable_fst (measurableSet_singleton _)
  have hTag : ∀ i, (μ i).real (T i) = 1 / (m : ℝ) := by
    intro i
    change (rawLaw κ m (a i) (b i) 1).real {z | z.1 = some (4 : Fin 5)} = _
    rw [measureReal_def, rawLaw_tag_mass hm1 (width_pos hm0 (ha i)) (ha' i)
      (width_pos hm0 (hb i)) (hb' i), ENNReal.toReal_ofReal (by positivity)]
  have hinv : 1 / (m : ℝ) ≤ 1 / 200 :=
    (div_le_div_iff₀ hm0 (by norm_num)).2 (by linarith)
  have hinvhalf : 1 / (2 * (m : ℝ)) = (1 / (m : ℝ)) / 2 := by ring
  have hSafe : ∀ i, ∀ᵐ z ∂μ i, z ∈ T i →
      z.2.1 < 1 - 3 / (m : ℝ) ∧ 3 / (m : ℝ) < z.2.2 := by
    intro i
    filter_upwards [rawLaw_ae_tag_interval κ m (a i) (b i) 1] with z hz
    intro ht
    obtain ⟨hx, hy⟩ := hz ht
    rw [hinvhalf] at hx hy
    rw [show (3 : ℝ) / m = 3 * (1 / (m : ℝ)) by ring]
    constructor <;> linarith
  have hdomX : ∀ i, (μ i).map (fun z => z.2.1) ≤
      ENNReal.ofReal 10 • volume.restrict (Ico (0 : ℝ) 1) := by
    intro i
    have h := rawLaw_map_endpoint_le_ten hκ0 hκ hm100 (ha i) (ha' i) (hb i) (hb' i)
      (t := 1) (by norm_num) (by norm_num) false
    change (μ i).map (fun z => z.2.1) ≤ (10 : ℝ≥0∞) • baseLaw at h
    simpa only [baseLaw_eq_restrict, show ENNReal.ofReal 10 = (10 : ℝ≥0∞) by norm_num] using h
  have hdomY : ∀ i, (μ i).map (fun z => z.2.2) ≤
      ENNReal.ofReal 10 • volume.restrict (Ico (0 : ℝ) 1) := by
    intro i
    have h := rawLaw_map_endpoint_le_ten hκ0 hκ hm100 (ha i) (ha' i) (hb i) (hb' i)
      (t := 1) (by norm_num) (by norm_num) true
    change (μ i).map (fun z => z.2.2) ≤ (10 : ℝ≥0∞) • baseLaw at h
    simpa only [baseLaw_eq_restrict, show ENNReal.ofReal 10 = (10 : ℝ≥0∞) by norm_num] using h
  have hbudget : 0 ≤ 1 - (1 + 2 * ((10 : ℝ) * 3)) / (m : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_one hm0).mpr (by linarith)
  have h := InvariantRotation.TruncationEvent.currentBlock_mass_lower_bound_ae m
    (by omega) μ T hT (fun _ => measurable_fst.comp measurable_snd)
    (fun _ => measurable_snd.comp measurable_snd) (C := 10) (a := 3)
    (by norm_num) (by norm_num) hbudget hTag hSafe hdomX hdomY
  norm_num only [show (1 : ℝ) + 2 * (10 * 3) = 61 by norm_num] at h
  exact (InvariantRotation.TaggedEventBounds.circle_tag_bound m hm).trans h

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleCurrentBlockEvent
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

private lemma coordinate_probability_for_tag (j i : ℕ) :
    IsProbabilityMeasure (coordinateLaw p j i) := by
  by_cases hi : i = 0
  · simp only [coordinateLaw, ite_eq_left hi, initialLaw]
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hs := p.blockIndex_pos hp.m_pos (show 1 ≤ i by omega)
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by have := hp.m_ge_200 _ hs; omega)
  have ht : 0 ≤ tag j (p.blockIndex i) ∧ tag j (p.blockIndex i) ≤ 1 := by
    unfold tag
    split_ifs <;> norm_num
  simpa only [coordinateLaw, ite_eq_right hi] using rawLaw_isProbabilityMeasure
    (CircleParameterLaws.coupling_kappa_bounds _ hs).1
    (CircleParameterLaws.coupling_kappa_bounds _ hs).2 hm
    (hp.coupling_a_bounds _ hs).1 (hp.coupling_a_bounds _ hs).2
    (hp.coupling_b_bounds _ hs).1 (hp.coupling_b_bounds _ hs).2 ht.1 ht.2

lemma coordinateLaw_currentBlock {j i : ℕ} (hi : i ∈ p.block j) :
    coordinateLaw p j i = rawLaw (kappa j) (p.m j) (p.a j) (p.b j) 1 := by
  have hi0 : i ≠ 0 := by
    have h := (p.mem_block_iff j i).mp hi
    omega
  simp only [coordinateLaw, ite_eq_right hi0, p.blockIndex_eq_of_mem hp.m_pos hi,
    tag, ite_true, if_true]

theorem rawCurrentBlockEvent_mass_lower (j : ℕ) (hj : 1 ≤ j) :
    Real.exp (-90) ≤ (law p j).real (rawCurrentBlockEvent p j) := by
  classical
  let := coordinate_probability_for_tag hp j
  let μ₀ := rawLaw (kappa j) (p.m j) (p.a j) (p.b j) 1
  have : IsProbabilityMeasure μ₀ := rawLaw_isProbabilityMeasure
    (CircleParameterLaws.coupling_kappa_bounds j hj).1
    (CircleParameterLaws.coupling_kappa_bounds j hj).2
    (by exact_mod_cast (show 100 ≤ p.m j by have := hp.m_ge_200 j hj; omega))
    (hp.coupling_a_bounds j hj).1 (hp.coupling_a_bounds j hj).2
    (hp.coupling_b_bounds j hj).1 (hp.coupling_b_bounds j hj).2
    (by norm_num) (by norm_num)
  let e : Fin (p.m j) ≃ (p.block j) := Fintype.equivOfCardEq (by simp [p.card_block j hj])
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin (p.m j) => CoordinateSample) e.symm
  let f : Sample → Fin (p.m j) → CoordinateSample := fun ω i => ω (e i)
  have hf : Measurable f := by unfold f; fun_prop
  have hcomp : f = E ∘ (p.block j).restrict := by
    funext ω i
    simp [E, f, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have hmap : (law p j).map f = Measure.pi (fun _ : Fin (p.m j) => μ₀) := by
    rw [hcomp, ← Measure.map_map E.measurable (Finset.measurable_restrict _)]
    change ((Measure.infinitePi (coordinateLaw p j)).map (p.block j).restrict).map E = _
    rw [Measure.infinitePi_map_restrict]
    have hcoord : (fun i : p.block j => coordinateLaw p j i) = fun _ => μ₀ := by
      funext i
      exact coordinateLaw_currentBlock hp i.property
    rw [hcoord]
    exact Measure.pi_map_piCongrLeft e.symm (fun _ : Fin (p.m j) => μ₀)
  let A : Set (Fin (p.m j) → CoordinateSample) :=
    {z | (∃ i, (z i).1 = some (4 : Fin 5)) ∧
      ∀ i, (z i).2.1 < 1 - 3 / (p.m j : ℝ) ∧ 3 / (p.m j : ℝ) < (z i).2.2}
  have hA : MeasurableSet A := by
    dsimp [A]
    measurability
  have hpre : f ⁻¹' A = rawCurrentBlockEvent p j := by
    ext ω
    constructor
    · rintro ⟨⟨i, hi⟩, hω⟩
      refine ⟨⟨e i, (e i).property, hi⟩, ?_⟩
      intro k hk
      obtain ⟨i, he⟩ := e.surjective ⟨k, hk⟩
      simpa only [f, he] using hω i
    · rintro ⟨⟨k, hk, htag⟩, hω⟩
      obtain ⟨i, he⟩ := e.surjective ⟨k, hk⟩
      refine ⟨⟨i, ?_⟩, ?_⟩
      · simpa only [f, he, label] using htag
      · intro i
        exact hω (e i) (e i).property
  have hmass : (law p j).real (rawCurrentBlockEvent p j) =
      (Measure.pi (fun _ : Fin (p.m j) => μ₀)).real A := by
    rw [← hmap]
    simp only [measureReal_def, Measure.map_apply hf hA, hpre]
  rw [hmass]
  exact concrete_circle_currentBlock_mass (p.m j) (hp.m_ge_200 j hj) (kappa j)
    (CircleParameterLaws.coupling_kappa_bounds j hj).1
    (CircleParameterLaws.coupling_kappa_bounds j hj).2
    (fun _ => p.a j) (fun _ => p.b j)
    (fun _ => (hp.coupling_a_bounds j hj).1) (fun _ => (hp.coupling_a_bounds j hj).2)
    (fun _ => (hp.coupling_b_bounds j hj).1) (fun _ => (hp.coupling_b_bounds j hj).2)

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleDigitEnergy
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

lemma rawLaw_map_endpoint {κ m a b t : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 100) (hm : 100 ≤ m)
    (ha : 1 / m ≤ a) (ha' : a ≤ 1 / 4)
    (hb : 1 / m ≤ b) (hb' : b ≤ 1 / 4)
    (ht0 : 0 ≤ t) (ht : t ≤ 1) (side : Bool) :
    (rawLaw κ m a b t).map (endpoint side) =
      baseLaw.withDensity (fun x => ENNReal.ofReal (marginalDensity side κ m a b t x)) := by
  have hm0 : 0 < m := by linarith
  have ha0 := width_pos hm0 ha
  have hb0 := width_pos hm0 hb
  have hq0 : 0 ≤ diagonalMass κ m a b t :=
    (by norm_num : (0 : ℝ) ≤ 49 / 50).trans
      (diagonalMass_bounds hκ0 hκ hm ha ha' hb hb' ht0 ht).1
  have : ∀ i, IsProbabilityMeasure (leftLaw (2 * m) a b i) :=
    leftLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  have : ∀ i, IsProbabilityMeasure (rightLaw (2 * m) a b i) :=
    rightLaw_isProbabilityMeasure (by linarith) ha0 ha' hb0 hb'
  cases side
  · change (rawLaw κ m a b t).map (Prod.fst ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_fst measurable_snd]
    unfold rawLaw
    rw [labelledMixture_map_snd]
    exact mixture_fst_real_density baseLaw _ _ _ _
      (leftDensity (2 * m) a b) hq0 (componentProbabilities_nonneg hκ0 hm0 ht0)
      (fun i x => (leftDensity_bound (by linarith) ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (leftLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb')
  · change (rawLaw κ m a b t).map (Prod.snd ∘ Prod.snd) = _
    rw [← Measure.map_map measurable_snd measurable_snd]
    unfold rawLaw
    rw [labelledMixture_map_snd]
    exact mixture_snd_real_density baseLaw _ _ _ _
      (rightDensity (2 * m) a b) hq0 (componentProbabilities_nonneg hκ0 hm0 ht0)
      (fun i x => (rightDensity_bound (by linarith) ha0 ha' hb0 hb' i x).1)
      (fun i => by fin_cases i <;> exact intervalDensity_measurable _ _)
      (rightLaw_eq_withDensity (by linarith) ha0 ha' hb0 hb')

end Invariant233.CircleDigitCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleFutureEndpointLoss
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace Invariant233.CircleCoupling
open CircleDigitCoupling CircleParameterData OneCoordinateCoupling
open InvariantRotation.EndpointIntervalBounds

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem coordinateLaw_raw_endpoint_le (j i : ℕ) (hi : 1 ≤ i) (side : Bool) :
    (coordinateLaw p j i).map (endpoint side) ≤ (10 : ℝ≥0∞) • baseLaw := by
  have hs := p.blockIndex_pos hp.m_pos hi
  have hm : (100 : ℝ) ≤ p.m (p.blockIndex i) := by
    exact_mod_cast (show 100 ≤ p.m (p.blockIndex i) by
      have := hp.m_ge_200 _ hs
      omega)
  have hk := CircleParameterLaws.coupling_kappa_bounds (p.blockIndex i) hs
  have ha := hp.coupling_a_bounds (p.blockIndex i) hs
  have hb := hp.coupling_b_bounds (p.blockIndex i) hs
  have ht := tag_bounds j (p.blockIndex i)
  rw [coordinateLaw, ite_eq_right (show i ≠ 0 by omega),
    rawLaw_map_endpoint hk.1 hk.2 hm ha.1 ha.2 hb.1 hb.2 ht.1 ht.2 side]
  apply withDensity_le_smul_of_ae_le
  exact Eventually.of_forall (fun x =>
    (ENNReal.ofReal_le_ofReal
      (CircleDigitCoupling.marginalDensity_bounds hk.1 hk.2 hm ha.1 ha.2 hb.1 hb.2
        ht.1 ht.2 side x).2.2.le).trans_eq (by norm_num))

theorem law_raw_endpoint_le (j i : ℕ) (hi : 1 ≤ i) (side : Bool) :
    (law p j).map (fun ω => endpoint side (ω i)) ≤ (10 : ℝ≥0∞) • baseLaw := by
  let := coordinateLaw_isProbabilityMeasure hp j
  have he : Measurable (endpoint side) := by
    cases side
    · exact measurable_fst.comp measurable_snd
    · exact measurable_snd.comp measurable_snd
  change (law p j).map (endpoint side ∘ (fun ω : Sample => ω i)) ≤ _
  rw [← Measure.map_map he (measurable_pi_apply i)]
  change ((Measure.infinitePi (coordinateLaw p j)).map (fun ω => ω i)).map _ ≤ _
  rw [Measure.infinitePi_map_eval]
  exact coordinateLaw_raw_endpoint_le hp j i hi side

theorem raw_endpoint_pair_loss_le (j i : ℕ) (hi : 1 ≤ i) (d : ℝ) (hd : 0 ≤ d) :
    (law p j).real {ω | 1 - d ≤ (ω i).2.1 ∨ (ω i).2.2 ≤ d} ≤ 20 * d := by
  have hx : Measurable (fun ω : Sample => (ω i).2.1) := by fun_prop
  have hy : Measurable (fun ω : Sample => (ω i).2.2) := by fun_prop
  have h := endpoint_pair_loss_le (law p j) hx hy (by norm_num : (0 : ℝ) ≤ 10) hd
    (by simpa only [endpoint, Bool.false_eq_true, ite_false, if_false, baseLaw_eq_restrict,
      ENNReal.ofReal_ofNat] using
      law_raw_endpoint_le hp j i hi false)
    (by simpa only [endpoint, ite_true, if_true, baseLaw_eq_restrict, ENNReal.ofReal_ofNat] using
      law_raw_endpoint_le hp j i hi true)
  norm_num only [show (2 : ℝ) * 10 = 20 by norm_num] at h
  exact h

theorem future_block_loss_le (j s : ℕ) (hs : 1 ≤ s) :
    (law p j).real (⋃ i ∈ p.block s,
      {ω | 1 - 3 * (p.K j : ℝ) / p.N s ≤ (ω i).2.1 ∨
        (ω i).2.2 ≤ 3 * (p.K j : ℝ) / p.N s}) ≤
      60 * (p.K j : ℝ) * (1 / (p.K s : ℝ)) := by
  let := law_isProbabilityMeasure hp j
  have hm : (0 : ℝ) < p.m s := by exact_mod_cast hp.m_pos s hs
  have hK : (0 : ℝ) < p.K s := by exact_mod_cast hp.K_pos s hs
  have hd : 0 ≤ 3 * (p.K j : ℝ) / p.N s := by
    unfold CircleParameterData.N
    positivity
  calc
    _ ≤ ∑ i ∈ p.block s, (law p j).real
        {ω | 1 - 3 * (p.K j : ℝ) / p.N s ≤ (ω i).2.1 ∨
          (ω i).2.2 ≤ 3 * (p.K j : ℝ) / p.N s} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ p.block s, 20 * (3 * (p.K j : ℝ) / p.N s) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := (p.mem_block_iff s i).mp hi
      exact raw_endpoint_pair_loss_le hp j i (by omega) _ hd
    _ = _ := by
      rw [Finset.sum_const, p.card_block s hs, nsmul_eq_mul]
      unfold CircleParameterData.N
      field_simp
      ring

theorem futureBadEvent_mass_le (j : ℕ) (hj : 1 ≤ j) :
    (law p j).real (futureBadEvent p j) ≤
      60 * (p.K j : ℝ) * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) := by
  let := law_isProbabilityMeasure hp j
  have hs : Summable (fun n : ℕ => 1 / (p.K (j + 1 + n) : ℝ)) := by
    have h := (summable_nat_add_iff j).mpr hp.summable_reciprocal
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have h := measureReal_iUnion_le_tsum_budget (law p j)
    (fun n => ⋃ i ∈ p.block (j + 1 + n),
      {ω | 1 - 3 * (p.K j : ℝ) / p.N (j + 1 + n) ≤ (ω i).2.1 ∨
        (ω i).2.2 ≤ 3 * (p.K j : ℝ) / p.N (j + 1 + n)})
    (b := fun n => 60 * (p.K j : ℝ) * (1 / (p.K (j + 1 + n) : ℝ)))
    (fun n => by positivity) (hs.mul_left (60 * (p.K j : ℝ)))
    (fun n => future_block_loss_le hp j (j + 1 + n) (by omega))
  simpa only [futureBadEvent, tsum_mul_left] using h

theorem futureBadEvent_mass_le_ratio (j : ℕ) (hj : 1 ≤ j) :
    (law p j).real (futureBadEvent p j) ≤
      120 * (p.K j : ℝ) / (p.K (j + 1) : ℝ) := by
  calc
    _ ≤ 60 * (p.K j : ℝ) * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) :=
      futureBadEvent_mass_le hp j hj
    _ ≤ 60 * (p.K j : ℝ) * (2 / (p.K (j + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.reciprocal_tail_bound j hj) (by positivity)
    _ = _ := by ring

omit hp in

theorem not_mem_futureBadEvent_iff (p : CircleParameterData) (j : ℕ) (ω : Sample) :
    ω ∉ futureBadEvent p j ↔ ∀ s : ℕ, j < s → ∀ i ∈ p.block s,
      (ω i).2.1 < 1 - 3 * (p.K j : ℝ) / p.N s ∧
        3 * (p.K j : ℝ) / p.N s < (ω i).2.2 := by
  simp only [futureBadEvent, Set.mem_iUnion, Set.mem_ofPred_eq, not_exists,
    not_or, not_le]
  constructor
  · intro h s hs i hi
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (show j + 1 ≤ s by omega)
    subst s
    exact h n i hi
  · intro h n i hi
    exact h (j + 1 + n) (by omega) i hi

end Invariant233.CircleCoupling

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem cutoff_le_sampling_horizon (j : ℕ) (hj : 1 ≤ j) :
    (p.K j : ℝ) ≤ p.Q j := by
  have hm : (200 : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_200 j hj
  have hKm : (p.K j : ℝ) ≤ p.m j := by exact_mod_cast hp.m_ge_K j hj
  apply hKm.trans
  unfold CircleParameterData.Q
  have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ p.m j by linarith)
    (show (1 : ℝ) ≤ (7 / 10 : ℝ) * p.m j by linarith)
  simpa only [Real.rpow_one] using h

theorem tendsto_successive_cutoff_ratio :
    Tendsto (fun n : ℕ => (p.K (n + 1) : ℝ) / (p.K (n + 2) : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero _ _ hp.tendsto_sampling_horizon
  · intro n
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro n
    exact div_le_div_of_nonneg_right (hp.cutoff_le_sampling_horizon (n + 1) (by omega))
      (Nat.cast_nonneg _)

end Invariant233.CircleParameterLaws

namespace Invariant233.CircleCoupling
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem tendsto_futureBadEvent_mass :
    Tendsto (fun n : ℕ => (law p (n + 1)).real (futureBadEvent p (n + 1)))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun n : ℕ =>
      120 * (p.K (n + 1) : ℝ) / (p.K (n + 2) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_div_assoc, mul_zero] using hp.tendsto_successive_cutoff_ratio.const_mul 120
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hlim
  intro n
  simpa only [Nat.add_assoc] using futureBadEvent_mass_le_ratio hp (n + 1) (by omega)

end Invariant233.CircleCoupling

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleTruncationMass
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology
namespace Invariant233.CircleCoupling

lemma truncationEvent_eq_current_sdiff (p : CircleParameterData) (j : ℕ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) :
    truncationEvent p j hr r = rawCurrentBlockEvent p j \
      (futureBadEvent p j ∪ centralBadEvent p j hr r) := by
  ext ω
  simp only [truncationEvent, rawCurrentBlockEvent, centralBadEvent, tagEvent,
    Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_union, not_or, not_lt,
    not_mem_futureBadEvent_iff]
  tauto

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem truncationEvent_mass_lower_sub_losses (j : ℕ) (hj : 1 ≤ j)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) (r : Circle → ℝ) :
    Real.exp (-90) - (law p j).real (futureBadEvent p j) -
      (law p j).real (centralBadEvent p j hr r) ≤
        (law p j).real (truncationEvent p j hr r) := by
  let := law_isProbabilityMeasure hp j
  rw [truncationEvent_eq_current_sdiff]
  have hcurrent := rawCurrentBlockEvent_mass_lower hp j hj
  have hunion := measureReal_union_le (μ := law p j)
    (futureBadEvent p j) (centralBadEvent p j hr r)
  have hdiff := le_measureReal_sdiff (μ := law p j)
    (s₁ := rawCurrentBlockEvent p j)
    (s₂ := futureBadEvent p j ∪ centralBadEvent p j hr r)
  linarith

theorem eventually_truncationEvent_mass
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ}
    (hrm : Measurable r) (hri : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
    ∀ᶠ j : ℕ in atTop,
      Real.exp (-90) / 2 ≤ (law p j).real (truncationEvent p j hr r) := by
  have hfuture : Tendsto (fun j : ℕ => (law p j).real (futureBadEvent p j))
      atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp (tendsto_futureBadEvent_mass hp)
  have hloss : Tendsto (fun j : ℕ => (law p j).real (futureBadEvent p j) +
      (law p j).real (centralBadEvent p j hr r)) atTop (𝓝 0) := by
    simpa only [zero_add] using hfuture.add (tendsto_centralBadEvent_mass hp hr hrm hri)
  have hsmall := hloss.eventually_lt_const
    (show (0 : ℝ) < Real.exp (-90) / 2 by positivity)
  filter_upwards [hsmall, eventually_ge_atTop 1] with j hj hjpos
  have hbound := truncationEvent_mass_lower_sub_losses hp j hjpos hr r
  linarith

theorem exists_truncationEvent_mass_threshold
    (hr : ∀ i, 0 < MixedRadix.radices p.q i) {r : Circle → ℝ}
    (hrm : Measurable r) (hri : ∀ᵐ x ∂volume, 0 < r x ∧ r x < 1) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
      Real.exp (-90) / 2 ≤ (law p j).real (truncationEvent p j hr r) := by
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (eventually_truncationEvent_mass hp hr hrm hri)
  exact ⟨max J 1, le_max_right _ _, fun j hj => hJ j ((le_max_left _ _).trans hj)⟩

end Invariant233.CircleCoupling

end

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

end Invariant233.PositiveDiagonalModel

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_RotationTrace
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.Rotation

theorem algebra_commutes_shiftedPullback_int (θ : ℝ) (r : ℤ)
    (T : Hilbert →L[ℂ] Hilbert) (hT : T ∈ algebra θ) :
    Commute T (DirectIntegral.shiftedPullback
      (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
      (action θ r) (action_measurePreserving θ r)) := by
  let S := (WeightedShift.shift r).toLinearIsometry.toContinuousLinearMap
  let S₁ := (WeightedShift.shift 1).toLinearIsometry.toContinuousLinearMap
  let J := DirectIntegral.shiftedPullback S (action θ r) (action_measurePreserving θ r)
  have hUJ : Commute U J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance U (fun _ => S₁)
      S (action θ r) (action_measurePreserving θ r) U_ae
    apply Filter.Eventually.of_forall
    intro x
    dsimp [S, S₁]
    rw [← WeightedShift.shift_add, ← WeightedShift.shift_add, add_comm (1 : ℤ) r]
  have hVJ : Commute (V θ) J := by
    apply FieldTraceCyclic.commute_shiftedPullback_of_covariance (V θ)
      (fun x => WeightedShift.diagonal (orbitWeight θ character x))
      S (action θ r) (action_measurePreserving θ r) (representation_ae θ character)
    apply Filter.Eventually.of_forall
    intro x
    ext v k
    change character (action θ k x) * v (k - r) =
      character (action θ (k - r) (action θ r x)) * v (k - r)
    simp only [action_add, sub_add_cancel]
  have hJ : J ∈ (algebra θ).commutant := by
    apply (mem_commutant_vonNeumannGenerated_iff _ _).mpr
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact ⟨hUJ.eq, (commute_star_left_of_mem_unitary U_mem_unitary hUJ).eq⟩
    · have hAV : A = V θ := Set.mem_singleton_iff.mp hA
      subst A
      exact ⟨hVJ.eq, (commute_star_left_of_mem_unitary (V_mem_unitary θ) hVJ).eq⟩
  exact (VonNeumannAlgebra.mem_commutant_iff.mp hJ) T hT

theorem vacuum_faithfulTracial (θ : ℝ) :
    IsFaithfulTracialVector (algebra θ) vacuum := by
  let b : HilbertBasis ℤ ℂ Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Fiber)
  have hb (k : ℤ) : b k = lp.single 2 k 1 := by
    rw [← HilbertBasis.repr_symm_single]
    rfl
  have hshift (r k : ℤ) :
      (WeightedShift.shift r).toLinearIsometry (b k) = b (k + r) := by
    rw [hb, hb]
    ext j
    change (lp.single 2 k (1 : ℂ) : Fiber) (j-r) = (lp.single 2 (k+r) (1 : ℂ) : Fiber) j
    simp only [lp.single_apply]
    simp only [Pi.single_apply]
    by_cases h : j - r = k
    · have h' : j = k + r := by omega
      rw [ite_eq_left h, ite_eq_left h']
    · have h' : j ≠ k + r := by omega
      rw [ite_eq_right h, ite_eq_right h']
  have h := FieldTraceCyclic.faithfulTracialVector_of_commuting_shiftedPullbacks
    b (algebra θ) (action θ) (action_measurePreserving θ)
    (fun r => (WeightedShift.shift r).toLinearIsometry) hshift
    (fun T hT r => algebra_commutes_shiftedPullback_int θ r T hT) ?_
  · simpa only [hb, vacuum] using h
  · intro T hT
    obtain ⟨A, hbound, hm, hrep, _⟩ := exists_unique_field hT
    exact ⟨A, hrep, fun r => (hm (b r)).aestronglyMeasurable,
      Filter.Eventually.of_forall hbound⟩

end Invariant233.Rotation

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_ParameterPositiveDiagonal
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem ae_strict_diagonal_measurableOperator (hθ : Irrational θ)
    (P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert)
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (htrace0 : 0 < (Rotation.vacuumFunctional P).re)
    (htrace1 : (Rotation.vacuumFunctional P).re < 1)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hbound : ∀ x, ‖F x‖ ≤ ‖P‖)
    (hmeas : ∀ v, StronglyMeasurable fun x => F x v)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂circleMeasure,
      0 < (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re ∧
      (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re < 1 := by
  let b : HilbertBasis ℤ ℂ Rotation.Fiber :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ Rotation.Fiber)
  let D : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber :=
    fun x => WeightedShift.diagonal (hp.parameterOrbitWeight x)
  let a : Circle → ℤ → ℝ := fun x k => p.measurableWeight θ (Rotation.action θ k x)
  have hb : ∀ x k, |a x k| ≤ 1 := by
    intro x k
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      p.measurableWeight_operator_bound θ hp (Rotation.action θ k x)
  have hw (x : Circle) : hp.parameterOrbitWeight x =
      PositiveDiagonalModel.realWeight a 1 hb x := by
    ext k
    rfl
  have hD : ∀ᵐ x ∂circleMeasure, IsSelfAdjoint (D x) := by
    apply Eventually.of_forall
    intro x
    dsimp [D]
    rw [hw]
    exact PositiveDiagonalModel.realWeight_diagonal_selfAdjoint a 1 hb x
  have heigen : ∀ᵐ x ∂circleMeasure,
      D x PositiveDiagonalModel.e0 =
        (p.measurableWeight θ x : ℂ) • PositiveDiagonalModel.e0 := by
    apply Eventually.of_forall
    intro x
    dsimp [D]
    rw [hw]
    simpa only [a, Rotation.action_zero, Complex.coe_smul] using
      PositiveDiagonalModel.realWeight_diagonal_e0 a 1 hb x
  have hT : ∀ ξ : Rotation.Hilbert, p.measurableOperator θ hp ξ =ᵐ[circleMeasure]
      fun x => ((PositiveDiagonalModel.fiberShiftUnit : Rotation.Fiber →L[ℂ] Rotation.Fiber) * D x) (ξ x) := by
    intro ξ
    exact hp.measurableOperator_ae ξ
  have hcov := DirectIntegral.ae_covariance_of_represented_commute b P F
    PositiveDiagonalModel.fiberShift (Rotation.action θ 1)
    (Rotation.action_measurePreserving θ 1) hrep
    (Rotation.algebra_commutes_shiftedPullback_int_independent θ 1 hPm)
  have hcov' : ∀ᵐ x ∂circleMeasure, F (Rotation.action θ 1 x) =
      ↑(PositiveDiagonalModel.fiberShiftUnit⁻¹) * F x *
        (PositiveDiagonalModel.fiberShiftUnit : Rotation.Fiber →L[ℂ] Rotation.Fiber) := by
    filter_upwards [hcov] with x hx
    have hh := congrArg (fun A : Rotation.Fiber →L[ℂ] Rotation.Fiber =>
      (↑(PositiveDiagonalModel.fiberShiftUnit⁻¹) : Rotation.Fiber →L[ℂ] Rotation.Fiber) * A) hx
    simpa only [← PositiveDiagonalModel.coe_fiberShiftUnit, ← mul_assoc,
      Units.inv_mul, one_mul] using hh.symm
  exact Fields.ae_strict_diagonal_of_represented_weighted_shift b
    (Rotation.action_one_ergodic hθ) P (p.measurableOperator θ hp) F D
    PositiveDiagonalModel.fiberShiftUnit ‖P‖ (norm_nonneg P) hbound hmeas hrep
    hT hP hinv hcov' PositiveDiagonalModel.norm_e0 hD
    (Eventually.of_forall (fun x => ne_of_gt (Real.exp_pos _)))
    heigen htrace0 htrace1

theorem ae_strict_diagonal_measurableOperator_of_nontrivial (hθ : Irrational θ)
    (P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert)
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hbound : ∀ x, ‖F x‖ ≤ ‖P‖)
    (hmeas : ∀ v, StronglyMeasurable fun x => F x v)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂circleMeasure,
      0 < (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re ∧
      (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re < 1 := by
  have htrace := strict_trace_bounds_of_nontrivial_projection
    (Rotation.algebra θ) Rotation.vacuum (Rotation.vacuum_faithfulTracial θ)
    P hPm hP hP0 hP1
  exact hp.ae_strict_diagonal_measurableOperator hθ P hPm hP hinv
    htrace.1 htrace.2 F hbound hmeas hrep

theorem exists_strict_rational_graph_field (hθ : Irrational θ)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      p.RationalGraphIdentities θ F ∧
      (∀ᵐ x ∂circleMeasure,
        0 < (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re ∧
        (inner ℂ PositiveDiagonalModel.e0 (F x PositiveDiagonalModel.e0)).re < 1) := by
  obtain ⟨F, hproj, hbound, hmeas, hrep, hgraph⟩ :=
    hp.exists_rational_graph_field hPm hP hinv
  exact ⟨F, hproj, hbound, hmeas, hrep, hgraph,
    hp.ae_strict_diagonal_measurableOperator_of_nontrivial hθ P hPm hP hinv
      hP0 hP1 F hbound hmeas hrep⟩

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_ProjectionTruncationMass
attribute [-instance] _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.OrderedProductCoupling.coordinateLaw_isProbabilityMeasure _root_.OAI.Invariant233.OrderedProductCoupling.law_isProbabilityMeasure _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
local notation "e₀" => PositiveDiagonalModel.e0

theorem exists_projection_truncation_mass_threshold (hθ : Irrational θ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    (P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert)
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1)
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hbound : ∀ x, ‖F x‖ ≤ ‖P‖)
    (hmeas : ∀ v, StronglyMeasurable fun x => F x v)
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
      Real.exp (-90) / 2 ≤ (CircleCoupling.law p j).real
        (CircleCoupling.truncationEvent p j hr
          (fun x => (inner ℂ e₀ (F x e₀)).re)) := by
  let r : Circle → ℝ := fun x => (inner ℂ e₀ (F x e₀)).re
  have hm : Measurable r :=
    ((Complex.continuous_re.comp (continuous_const.inner continuous_id)).comp_stronglyMeasurable
      (hmeas e₀)).measurable
  have hi : ∀ᵐ x ∂(volume : Measure Circle), 0 < r x ∧ r x < 1 :=
    hp.ae_strict_diagonal_measurableOperator_of_nontrivial hθ P hPm hP hinv
      hP0 hP1 F hbound hmeas hrep
  exact CircleCoupling.exists_truncationEvent_mass_threshold hp hr (r := r) hm hi

theorem exists_rational_graph_field_with_truncation_mass_oai (hθ : Irrational θ)
    (hr : ∀ i, 0 < MixedRadix.radices p.q i)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hPm : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hinv : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hP0 : P ≠ 0) (hP1 : P ≠ 1) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      p.RationalGraphIdentities θ F ∧
      ∃ J : ℕ, 1 ≤ J ∧ ∀ j : ℕ, J ≤ j →
        Real.exp (-90) / 2 ≤ (CircleCoupling.law p j).real
          (CircleCoupling.truncationEvent p j hr
            (fun x => (inner ℂ e₀ (F x e₀)).re)) := by
  obtain ⟨F, hproj, hbound, hmeas, hrep, hgraph, _⟩ :=
    hp.exists_strict_rational_graph_field hθ hPm hP hinv hP0 hP1
  exact ⟨F, hproj, hbound, hmeas, hrep, hgraph,
    hp.exists_projection_truncation_mass_threshold hθ hr P hPm hP hinv hP0 hP1
      F hbound hmeas hrep⟩

end Invariant233.CircleParameterLaws

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass_oai := @OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_with_truncation_mass_oai
