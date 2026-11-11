-- Prove2me | solution 1 for OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T19:26:57.391763+00:00
-- url     : https://prove2.me/submissions/0733dd61-4df2-4d5e-b8b2-39809d493a10

import Mathlib
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.Algebra.Group.Idempotent
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Int.Interval
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.Dynamics.Ergodic.AddCircleAdd
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.NumberTheory.Real.Irrational
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
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Lattice
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.TietzeExtension
import Mathlib.Topology.UniformSpace.UniformApproximation
import Definitions.Def_IrrationalRotation
import Definitions.Def_Q234IR003

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CappedRatios
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233

variable {X : Type*}

theorem continuousOn_capped_ratio [TopologicalSpace X]
    (F : X → ℝ) (Q : Set X) (hF : ContinuousOn F Q)
    (hFp : ∀ x ∈ Q, F x ≠ 0) (B : ℝ) :
    ContinuousOn (fun t : X × X => (Complex.ofReal (min B (F t.2 / F t.1)))) (Q ×ˢ Q) := by
  have hfst : ContinuousOn (fun t : X × X => F t.1) (Q ×ˢ Q) :=
    hF.comp continuous_fst.continuousOn (fun _ ht => ht.1)
  have hsnd : ContinuousOn (fun t : X × X => F t.2) (Q ×ˢ Q) :=
    hF.comp continuous_snd.continuousOn (fun _ ht => ht.2)
  have hratio : ContinuousOn (fun t : X × X => F t.2 / F t.1) (Q ×ˢ Q) :=
    hsnd.div hfst (fun t ht => hFp t.1 ht.1)
  exact Complex.continuous_ofReal.comp_continuousOn (continuousOn_const.inf hratio)

end Invariant233

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace Invariant233.CompactTransfer

theorem measure_compl_le_of_tendsto {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} [L.NeBot]
    {ν : FiniteMeasure X} {νs : ι → FiniteMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {K : Set X} (hK : IsClosed K)
    {ε : ℝ≥0∞} (hbound : ∀ᶠ i in L, (νs i : Measure X) Kᶜ ≤ ε) :
    (ν : Measure X) Kᶜ ≤ ε := by
  have hmass : Tendsto (fun i => (νs i : Measure X) Set.univ) L
      (𝓝 ((ν : Measure X) Set.univ)) := by
    simpa only [← FiniteMeasure.ennreal_mass, Function.comp_def] using
      ENNReal.continuous_coe.continuousAt.tendsto.comp hν.mass
  have hparts : ∀ᶠ i in L,
      (νs i : Measure X) Set.univ ≤ (νs i : Measure X) K + ε := by
    filter_upwards [hbound] with i hi
    rw [← measure_add_measure_compl hK.measurableSet]
    exact add_le_add le_rfl hi
  have hlim := Filter.limsup_le_limsup hparts
  rw [hmass.limsup_eq,
    limsup_add_const L (fun i => (νs i : Measure X) K) ε
      (by isBoundedDefault) (by isBoundedDefault)] at hlim
  have htotal := hlim.trans (add_le_add
    (FiniteMeasure.limsup_measure_closed_le_of_tendsto hν hK) le_rfl)
  rw [measure_compl hK.measurableSet (measure_ne_top _ _), tsub_le_iff_right]
  simpa only [add_comm] using htotal

theorem ae_mem_of_closed_approximation {X ι : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    [HasOuterApproxClosed X] {L : Filter ι} [L.NeBot]
    {ν : FiniteMeasure X} {νs : ι → FiniteMeasure X}
    (hν : Tendsto νs L (𝓝 ν)) {S : Set X}
    (happrox : ∀ ε : ℝ≥0, 0 < ε → ∃ K : Set X,
      IsClosed K ∧ K ⊆ S ∧ ∀ᶠ i in L, (νs i : Measure X) Kᶜ ≤ ε) :
    ∀ᵐ x ∂(ν : Measure X), x ∈ S := by
  apply ae_iff.mpr
  change (ν : Measure X) Sᶜ = 0
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨K, hK, hKS, hbound⟩ := happrox ε hε
  simpa using
    (measure_mono (Set.compl_subset_compl.mpr hKS)).trans
      (measure_compl_le_of_tendsto hν hK hbound)

end Invariant233.CompactTransfer

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_CountableGraphTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory

namespace Invariant233.Fields

variable {X Y Ω ι : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [Countable ι] {μ : Measure X} {ν : Measure Ω}

theorem ae_relation_of_countable_graphs
    (P : X → Y → Prop) (t : ι → X → Y) (x : Ω → X) (y : Ω → Y)
    (hx : AEMeasurable x ν) (hμ : ν.map x ≪ μ)
    (hgraph : ∀ i, ∀ᵐ z ∂μ, P z (t i z))
    (hsupport : ∀ᵐ ω ∂ν, ∃ i, y ω = t i (x ω)) :
    ∀ᵐ ω ∂ν, P (x ω) (y ω) := by
  have hcommon : ∀ᵐ z ∂μ, ∀ i, P z (t i z) := ae_all_iff.mpr hgraph
  have hpull : ∀ᵐ ω ∂ν, ∀ i, P (x ω) (t i (x ω)) :=
    ae_of_ae_map hx (hμ.ae_le hcommon)
  filter_upwards [hpull, hsupport] with ω hω hωsupport
  obtain ⟨i, hi⟩ := hωsupport
  rw [hi]
  exact hω i

theorem ae_pair_relation_of_countable_graphs [MeasurableSpace Y]
    {β : Measure (X × Y)} (P : X → Y → Prop) (t : ι → X → Y)
    (hμ : β.map Prod.fst ≪ μ)
    (hgraph : ∀ i, ∀ᵐ z ∂μ, P z (t i z))
    (hsupport : ∀ᵐ z ∂β, ∃ i, z.2 = t i z.1) :
    ∀ᵐ z ∂β, P z.1 z.2 :=
  ae_relation_of_countable_graphs P t Prod.fst Prod.snd
    measurable_fst.aemeasurable hμ hgraph hsupport

end Invariant233.Fields

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_DensityMeasureConvergence
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology ENNReal

namespace Invariant233.GraphMeasureConvergence

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]

theorem tendsto_of_density_L1
    (μ : FiniteMeasure X) (ν : ℕ → FiniteMeasure X) (ρ : ℕ → X → ℝ)
    (hρ : ∀ n, Integrable (ρ n) (μ : Measure X))
    (hnonneg : ∀ n, 0 ≤ᵐ[(μ : Measure X)] ρ n)
    (hν : ∀ n, (ν n : Measure X) =
      (μ : Measure X).withDensity (fun x => ENNReal.ofReal (ρ n x)))
    (hL1 : Tendsto (fun n => ∫ x, ‖ρ n x - 1‖ ∂(μ : Measure X)) atTop (𝓝 0)) :
    Tendsto ν atTop (𝓝 μ) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have heq (n : ℕ) : (∫ x, f x ∂(ν n : Measure X)) -
      (∫ x, f x ∂(μ : Measure X)) =
      ∫ x, (ρ n x - 1) * f x ∂(μ : Measure X) := by
    rw [hν n, integral_withDensity_eq_integral_toReal_smul₀
      (hρ n).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have hprod : Integrable (fun x => ρ n x * f x) (μ : Measure X) :=
      (hρ n).mul_bdd f.continuous.measurable.aestronglyMeasurable
        (Eventually.of_forall fun x => f.norm_coe_le_norm x)
    have hi : (∫ x, (ENNReal.ofReal (ρ n x)).toReal • f x ∂(μ : Measure X)) =
        ∫ x, ρ n x * f x ∂(μ : Measure X) := by
      apply integral_congr_ae
      filter_upwards [hnonneg n] with x hx
      simp only [ENNReal.toReal_ofReal hx, smul_eq_mul]
    rw [hi, ← integral_sub hprod (f.integrable _)]
    congr 1
    funext x
    ring
  have hbound (n : ℕ) :
      ‖(∫ x, f x ∂(ν n : Measure X)) - (∫ x, f x ∂(μ : Measure X))‖ ≤
      (∫ x, ‖ρ n x - 1‖ ∂(μ : Measure X)) * ‖f‖ := by
    rw [heq]
    calc
      ‖∫ x, (ρ n x - 1) * f x ∂(μ : Measure X)‖ ≤
          ∫ x, ‖ρ n x - 1‖ * ‖f‖ ∂(μ : Measure X) := by
        apply norm_integral_le_of_norm_le (((hρ n).sub (integrable_const 1)).norm.mul_const ‖f‖)
        exact Eventually.of_forall fun x => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (norm_nonneg _)
      _ = (∫ x, ‖ρ n x - 1‖ ∂(μ : Measure X)) * ‖f‖ := integral_mul_const _ _
  have hdiff := squeeze_zero_norm hbound (by simpa only [zero_mul] using hL1.mul_const ‖f‖)
  have hsum := hdiff.add (tendsto_const_nhds (x := ∫ x, f x ∂(μ : Measure X)))
  simpa only [sub_add_cancel, zero_add] using hsum

theorem tendsto_of_density_L2
    (μ : FiniteMeasure X) [IsProbabilityMeasure (μ : Measure X)]
    (ν : ℕ → FiniteMeasure X) (ρ : ℕ → X → ℝ)
    (hρ : ∀ n, MemLp (ρ n) 2 (μ : Measure X))
    (hnonneg : ∀ n, 0 ≤ᵐ[(μ : Measure X)] ρ n)
    (hν : ∀ n, (ν n : Measure X) =
      (μ : Measure X).withDensity (fun x => ENNReal.ofReal (ρ n x)))
    (hL2 : Tendsto (fun n => eLpNorm (fun x => ρ n x - 1) 2 (μ : Measure X))
      atTop (𝓝 0)) : Tendsto ν atTop (𝓝 μ) := by
  apply tendsto_of_density_L1 μ ν ρ (fun n => (hρ n).integrable (by norm_num)) hnonneg hν
  have he (n : ℕ) : MemLp (fun x => ρ n x - 1) 2 (μ : Measure X) :=
    (hρ n).sub (memLp_const 1)
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => ?_) (by simpa only [ENNReal.toReal_zero] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL2)
  rw [integral_norm_eq_lintegral_enorm (he n).aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm]
  exact ENNReal.toReal_mono (he n).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (hf := (he n).aestronglyMeasurable) (by norm_num))

end Invariant233.GraphMeasureConvergence

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_EndpointLoss
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace

namespace Invariant233.EndpointLoss

variable {X : Type*} [MeasurableSpace X]

theorem sqrt_integral_sq_eq_norm {μ : Measure X} (f : Lp ℝ 2 μ) :
    Real.sqrt (∫ x, f x ^ 2 ∂μ) = ‖f‖ := by
  have hs : (∫ x, f x ^ 2 ∂μ) = ‖f‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [hs, Real.sqrt_sq (norm_nonneg f)]

theorem sqrt_integral_sq_eq_toReal_eLpNorm {μ : Measure X} {h : X → ℝ} (hh : MemLp h 2 μ) :
    Real.sqrt (∫ x, h x ^ 2 ∂μ) = (eLpNorm h 2 μ).toReal := by
  rw [← Lp.norm_toLp h hh, ← sqrt_integral_sq_eq_norm]
  congr 1
  apply integral_congr_ae
  filter_upwards [hh.coeFn_toLp] with x hx
  rw [hx]

theorem setIntegral_density_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (∫ x in s, h x ∂μ) ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    Real.HolderConjugate.two_two h_nonneg
    (show 0 ≤ᵐ[μ] s.indicator (fun _ : X => (1 : ℝ)) from
      Filter.Eventually.of_forall (fun x => by
        change 0 ≤ s.indicator (fun _ : X => (1 : ℝ)) x
        by_cases hx : x ∈ s <;> simp [hx]))
    (by simpa using hh) (by simpa using (MemLp.indicator hs (memLp_const (1 : ℝ))))
  have hmul : (fun x => h x * s.indicator (fun _ : X => (1 : ℝ)) x) =
      s.indicator h := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  have hpow : (fun x => (s.indicator (fun _ : X => (1 : ℝ)) x) ^ (2 : ℝ)) =
      s.indicator (fun _ : X => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [hmul, integral_indicator hs, hpow] at hCS
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hCS
  have hmass : (∫ x, s.indicator (fun _ : X => (1 : ℝ)) x ∂μ) = μ.real s := by
    rw [integral_indicator hs]
    simp
  simpa only [hmass] using hCS

theorem withDensity_measureReal_le_sqrt
    (μ : Measure X) [IsFiniteMeasure μ] {h : X → ℝ}
    (hh : MemLp h 2 μ) (h_nonneg : 0 ≤ᵐ[μ] h)
    {s : Set X} (hs : MeasurableSet s) :
    (μ.withDensity (fun x => ENNReal.ofReal (h x))).real s ≤
      Real.sqrt (∫ x, h x ^ 2 ∂μ) * Real.sqrt (μ.real s) := by
  rw [measureReal_def, withDensity_apply _ hs]
  rw [← integral_eq_lintegral_of_nonneg_ae
    (ae_restrict_of_ae h_nonneg) hh.aestronglyMeasurable.restrict]
  exact setIntegral_density_le_sqrt μ hh h_nonneg hs

end Invariant233.EndpointLoss

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformAbsoluteContinuityLimits
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace Invariant233.UniformlyAbsolutelyContinuous

variable {X ι : Type*} [MeasurableSpace X]

theorem mono {μ : Measure X} {ν η : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν) (hην : ∀ i, η i ≤ ν i) :
    UniformlyAbsolutelyContinuous μ η := by
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := hν ε hε
  exact ⟨δ, hδ, fun A hA hμ i => (hην i A).trans_lt (hsmall A hA hμ i)⟩

theorem map_restrict {Z : Type*} [MeasurableSpace Z]
    {μ : Measure X} {ν : ι → Measure Z} (f : Z → X) (hf : Measurable f)
    (hν : UniformlyAbsolutelyContinuous μ (fun i => (ν i).map f))
    (s : ι → Set Z) :
    UniformlyAbsolutelyContinuous μ (fun i => ((ν i).restrict (s i)).map f) :=
  hν.mono (fun _ => Measure.map_mono Measure.restrict_le_self hf)

theorem tendsto_apply_of_base_tendsto_zero
    {μ : Measure X} {ν : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν)
    {L : Filter ι} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hbase : Tendsto (fun i => μ (s i)) L (𝓝 0)) :
    Tendsto (fun i => ν i (s i)) L (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨η, hη, hηε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  obtain ⟨δ, hδ, hsmall⟩ := hν η (ENNReal.coe_pos.mp hη)
  have hδ' : (0 : ℝ≥0∞) < δ := ENNReal.coe_pos.mpr hδ
  filter_upwards [hbase.eventually_lt_const hδ'] with i hi
  exact (hsmall (s i) (hs i) hi i).le.trans hηε.le

theorem tendsto_real_apply_of_base_tendsto_zero
    {μ : Measure X} {ν : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν)
    {L : Filter ι} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hbase : Tendsto (fun i => μ (s i)) L (𝓝 0)) :
    Tendsto (fun i => (ν i).real (s i)) L (𝓝 0) := by
  simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      (hν.tendsto_apply_of_base_tendsto_zero s hs hbase)

theorem tendsto_real_apply_of_base_real_tendsto_zero
    {μ : Measure X} [IsFiniteMeasure μ] {ν : ι → Measure X}
    (hν : UniformlyAbsolutelyContinuous μ ν)
    {L : Filter ι} (s : ι → Set X) (hs : ∀ i, MeasurableSet (s i))
    (hbase : Tendsto (fun i => μ.real (s i)) L (𝓝 0)) :
    Tendsto (fun i => (ν i).real (s i)) L (𝓝 0) := by
  apply hν.tendsto_real_apply_of_base_tendsto_zero s hs
  have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp hbase
  simpa only [Function.comp_def, Measure.real, ENNReal.ofReal_toReal (measure_ne_top μ _),
    ENNReal.ofReal_zero] using h

end Invariant233.UniformlyAbsolutelyContinuous

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_GraphMeasureConvergence
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Filter Set BoundedContinuousFunction
open scoped Topology

namespace Invariant233.GraphMeasureConvergence

variable {X Y : Type*}
    [PseudoMetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [PseudoMetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]

theorem tendsto_integral_sub_graph
    (ν : ℕ → FiniteMeasure (X × Y)) (g : X → Y) (hg : Continuous g)
    (M : ℝ) (hM : ∀ᶠ n in atTop, (ν n : Measure (X × Y)).real univ ≤ M)
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ)
    (f : (X × Y) →ᵇ ℝ) :
    Tendsto (fun n => (∫ z, f z ∂(ν n : Measure (X × Y))) -
      ∫ z, f (z.1, g z.1) ∂(ν n : Measure (X × Y))) atTop (𝓝 0) := by
  let B : ℝ := |M| + 1
  have hB : 0 < B := by dsimp [B] <;> positivity
  let G : C(X × Y, X × Y) :=
    ⟨fun z => (z.1, g z.1), continuous_fst.prodMk (hg.comp continuous_fst)⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hη : 0 < ε / (2 * B) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous f.continuous) (ε / (2 * B)) hη
  filter_upwards [hM, hnear δ hδ] with n hn hclose
  have hpoint : ∀ᵐ z ∂(ν n : Measure (X × Y)),
      ‖f z - f (z.1, g z.1)‖ ≤ ε / (2 * B) := by
    filter_upwards [hclose] with z hz
    have hd : dist z (z.1, g z.1) < δ := by
      simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hz
    simpa only [dist_eq_norm] using (hδf hd).le
  have hfg : Integrable (fun z : X × Y => f (z.1, g z.1))
      (ν n : Measure (X × Y)) := (f.compContinuous G).integrable _
  rw [dist_zero_right, ← integral_sub (f.integrable _) hfg]
  calc
    ‖∫ z, f z - f (z.1, g z.1) ∂(ν n : Measure (X × Y))‖ ≤
        (ε / (2 * B)) * (ν n : Measure (X × Y)).real univ :=
      norm_integral_le_of_norm_le_const hpoint
    _ ≤ (ε / (2 * B)) * B := by
      apply mul_le_mul_of_nonneg_left _ hη.le
      exact hn.trans (by dsimp [B] <;> linarith [le_abs_self M])
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

theorem tendsto_graph_of_first_marginal
    (ν : ℕ → FiniteMeasure (X × Y)) (μ : FiniteMeasure X)
    (g : X → Y) (hg : Continuous g)
    (hfirst : Tendsto (fun n => (ν n).map Prod.fst) atTop (𝓝 μ))
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ) :
    Tendsto ν atTop (𝓝 (μ.map (fun x => (x, g x)))) := by
  have hmass : Tendsto (fun n => (ν n : Measure (X × Y)).real univ)
      atTop (𝓝 ((μ : Measure X).real univ)) := by
    have h := NNReal.continuous_coe.continuousAt.tendsto.comp hfirst.mass
    simpa only [Function.comp_def, FiniteMeasure.measureReal_eq_coe_coeFn,
      FiniteMeasure.mass, FiniteMeasure.map_apply _ measurable_fst MeasurableSet.univ,
      Set.preimage_univ] using h
  let M := (μ : Measure X).real univ + 1
  have hM : ∀ᶠ n in atTop, (ν n : Measure (X × Y)).real univ ≤ M :=
    (hmass.eventually_lt_const (by dsimp [M] <;> linarith)).mono (fun _ h => h.le)
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  let G : C(X, X × Y) := ⟨fun x => (x, g x), continuous_id.prodMk hg⟩
  have hgraph := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hfirst
    (f.compContinuous G)
  have heq : ∀ n, (∫ x, (f.compContinuous G) x ∂((ν n).map Prod.fst : Measure X)) =
      ∫ z, f (z.1, g z.1) ∂(ν n : Measure (X × Y)) := by
    intro n
    exact integral_map measurable_fst.aemeasurable
      ((f.compContinuous G).continuous.measurable.aestronglyMeasurable)
  simp_rw [heq] at hgraph
  have hlim := (tendsto_integral_sub_graph ν g hg M hM hnear f).add hgraph
  have hmap : (∫ z, f z ∂(μ.map (fun x => (x, g x)) : Measure (X × Y))) =
      ∫ x, (f.compContinuous G) x ∂(μ : Measure X) :=
    integral_map (continuous_id.prodMk hg).measurable.aemeasurable
      f.continuous.measurable.aestronglyMeasurable
  rw [hmap]
  simpa only [sub_add_cancel, zero_add] using hlim

theorem tendsto_restrict_of_compl_mass_tendsto_zero
    {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z] [OpensMeasurableSpace Z]
    (ν : ℕ → FiniteMeasure Z) (μ : FiniteMeasure Z)
    (hν : Tendsto ν atTop (𝓝 μ)) (s : ℕ → Set Z)
    (hs : ∀ n, MeasurableSet (s n))
    (hremoved : Tendsto (fun n => (ν n : Measure Z).real (s n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (ν n).restrict (s n)) atTop (𝓝 μ) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hdiff : Tendsto (fun n => (∫ z, f z ∂(ν n : Measure Z)) -
      ∫ z in s n, f z ∂(ν n : Measure Z)) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun n => norm_integral_sub_setIntegral_le
        (Eventually.of_forall fun z => f.norm_coe_le_norm z) (hs n) (f.integrable _))
    simpa only [zero_mul] using hremoved.mul_const ‖f‖
  have htest := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν f
  simpa only [sub_sub_cancel, sub_zero, FiniteMeasure.restrict_measure_eq] using htest.sub hdiff

theorem tendsto_trimmed_graph_of_first_marginal
    (ν : ℕ → FiniteMeasure (X × Y)) (μ : FiniteMeasure X)
    (g : X → Y) (hg : Continuous g)
    (hfirst : Tendsto (fun n => (ν n).map Prod.fst) atTop (𝓝 μ))
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ)
    (s : ℕ → Set (X × Y)) (hs : ∀ n, MeasurableSet (s n))
    (hremoved : Tendsto (fun n => (ν n : Measure (X × Y)).real (s n)ᶜ)
      atTop (𝓝 0)) :
    Tendsto (fun n => (ν n).restrict (s n)) atTop
      (𝓝 (μ.map (fun x => (x, g x)))) :=
  tendsto_restrict_of_compl_mass_tendsto_zero ν _
    (tendsto_graph_of_first_marginal ν μ g hg hfirst hnear) s hs hremoved

theorem tendsto_trimmed_graph_of_uniform_first_marginal
    (ν : ℕ → FiniteMeasure (X × Y)) (μ : FiniteMeasure X)
    (g : X → Y) (hg : Continuous g)
    (hfirst : Tendsto (fun n => (ν n).map Prod.fst) atTop (𝓝 μ))
    (hnear : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ z ∂(ν n : Measure (X × Y)), dist z.2 (g z.1) < δ)
    (huac : UniformlyAbsolutelyContinuous (μ : Measure X)
      (fun n => (ν n : Measure (X × Y)).map Prod.fst))
    (s : ℕ → Set X) (hs : ∀ n, MeasurableSet (s n))
    (hbase : Tendsto (fun n => (μ : Measure X).real (s n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (ν n).restrict (Prod.fst ⁻¹' s n)) atTop
      (𝓝 (μ.map (fun x => (x, g x)))) := by
  apply tendsto_trimmed_graph_of_first_marginal ν μ g hg hfirst hnear
    (fun n => Prod.fst ⁻¹' s n) (fun n => (hs n).preimage measurable_fst)
  have h := huac.tendsto_real_apply_of_base_real_tendsto_zero
    (fun n => (s n)ᶜ) (fun n => (hs n).compl) hbase
  have heq (n : ℕ) : ((ν n : Measure (X × Y)).map Prod.fst).real (s n)ᶜ =
      (ν n : Measure (X × Y)).real (Prod.fst ⁻¹' s n)ᶜ := by
    rw [map_measureReal_apply measurable_fst (hs n).compl]
    rfl
  simpa only [heq] using h

end Invariant233.GraphMeasureConvergence

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

theorem ae_all_int_finite_floor_support {ι : Type*} [Countable ι]
    (q : ι → ℤ) (hq : ∀ i, q i ≠ 0)
    (α : ι → ℝ) (hα0 : ∀ i, 0 ≤ α i) (hα : Summable α) :
    ∀ᵐ x ∂(volume : Measure UnitAddCircle), ∀ k : ℤ,
      (Function.support (fun i =>
        Int.floor (((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ) +
          (k : ℝ) * α i))).Finite := by
  exact FiniteSupportWeights.ae_all_finite_floor_support volume
    (fun i x => ((AddCircle.equivIco (1 : ℝ) 0 (q i • x)) : ℝ))
    (fun i => measurePreserving_characterRepresentative (q i) (hq i)) α hα0 hα

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

theorem floor_sub_eq_crossing {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (t : ℝ) :
    ⌊w + t⌋ - ⌊u + t⌋ =
      if u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w then 1 else 0 := by
  rw [floor_add_eq_indicator hw₀ hw₁, floor_add_eq_indicator hu₀ hu₁]
  by_cases huT : 1 - Int.fract t ≤ u
  · have hwT : 1 - Int.fract t ≤ w := huT.trans huw
    simp [huT, hwT, not_lt_of_ge huT]
  · have hut : u < 1 - Int.fract t := lt_of_not_ge huT
    by_cases hwT : 1 - Int.fract t ≤ w
    · simp [huT, hwT, hut]
    · simp [huT, hwT]

theorem floor_sub_eq_one_iff {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1)
    (huw : u ≤ w) (t : ℝ) :
    ⌊w + t⌋ - ⌊u + t⌋ = 1 ↔
      u < 1 - Int.fract t ∧ 1 - Int.fract t ≤ w := by
  rw [floor_sub_eq_crossing hu₀ hu₁ hw₀ hw₁ huw]
  split_ifs <;> simp_all

theorem floor_sub_bounds {u w : ℝ}
    (hu₀ : 0 ≤ u) (hu₁ : u < 1) (hw₀ : 0 ≤ w) (hw₁ : w < 1) (t : ℝ) :
    -1 ≤ ⌊w + t⌋ - ⌊u + t⌋ ∧ ⌊w + t⌋ - ⌊u + t⌋ ≤ 1 := by
  rw [floor_add_eq_indicator hw₀ hw₁, floor_add_eq_indicator hu₀ hu₁]
  split_ifs <;> omega

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
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
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

theorem zsmul_rational_eq_zero {q d : ℤ} (hd : d ≠ 0) (hdq : d ∣ q) (r : ℤ) :
    q • (((r : ℝ) / (d : ℝ) : ℝ) : Circle) = 0 := by
  obtain ⟨k, rfl⟩ := hdq
  rw [← AddCircle.coe_zsmul, zsmul_eq_mul]
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  have he : ((d * k : ℤ) : ℝ) * ((r : ℝ) / (d : ℝ)) = ((k * r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [he]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨k * r, ?_⟩
  simp [zsmul_eq_mul]

theorem character_rational_translation {q d : ℤ} (hd : d ≠ 0) (hdq : d ∣ q)
    (r : ℤ) (x : Circle) :
    rep (q • (x + (((r : ℝ) / (d : ℝ) : ℝ) : Circle))) = rep (q • x) := by
  rw [zsmul_add, zsmul_rational_eq_zero hd hdq r, add_zero]

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

theorem cocycle_pos (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (k : ℤ) (x : UnitAddCircle) : 0 < cocycle θ q c k x := Real.exp_pos _

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

theorem orbit_ratio_of_cocycle_identities (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ)
    (x : UnitAddCircle) (v n : ℤ)
    (hvn : cocycle θ q c (v + n) x =
      cocycle θ q c n (rotate θ v x) * cocycle θ q c v x)
    (hnv : cocycle θ q c (n + v) x =
      cocycle θ q c v (rotate θ n x) * cocycle θ q c n x) :
    cocycle θ q c n (rotate θ v x) / cocycle θ q c n x =
      cocycle θ q c v (rotate θ n x) / cocycle θ q c v x := by
  apply (div_eq_div_iff (ne_of_gt (cocycle_pos θ q c n x))
    (ne_of_gt (cocycle_pos θ q c v x))).mpr
  rw [← hvn, ← hnv, add_comm v n]

end Invariant233.CircleWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_InfiniteRatioCaps
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Function
open scoped BigOperators

namespace Invariant233.InfiniteRatioCaps

private theorem summable_finset_mask {I : Type*} [DecidableEq I] (c : I → ℝ) (s : Finset I) :
    Summable (fun i => if i ∈ s then c i else 0) := by
  classical
  apply summable_of_hasFiniteSupport
  apply s.finite_toSet.subset
  intro i hi
  by_contra hn
  change i ∉ s at hn
  exact hi (by simp [hn])

private theorem tsum_finset_mask {I : Type*} [DecidableEq I] (c : I → ℝ) (s : Finset I) :
    (∑' i, if i ∈ s then c i else 0) = ∑ i ∈ s, c i := by
  classical
  rw [tsum_eq_sum (s := s) (by intro i hi; simp [hi])]
  exact Finset.sum_congr rfl (by intro i hi; simp [hi])

theorem ratio_le_exp_exception_sub_crossings {I : Type*}
    (x y t c : I → ℝ) (a s : Finset I)
    (hx01 : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy01 : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1)
    (hc : ∀ i, 0 ≤ c i) (hxy : ∀ i, i ∉ a → x i ≤ y i)
    (hx : HasFiniteSupport (fun i => Int.floor (x i + t i)))
    (hy : HasFiniteSupport (fun i => Int.floor (y i + t i)))
    (hcross : ∀ i ∈ s, x i < 1 - Int.fract (t i) ∧
      1 - Int.fract (t i) ≤ y i) :
    Real.exp (-(∑' i, c i * (Int.floor (y i + t i) : ℝ))) /
      Real.exp (-(∑' i, c i * (Int.floor (x i + t i) : ℝ))) ≤
      Real.exp ((∑ i ∈ a, c i) - ∑ i ∈ s, c i) := by
  classical
  have hsx := FiniteSupportCocycle.summable_weighted_int c hx
  have hsy := FiniteSupportCocycle.summable_weighted_int c hy
  have hbound (i : I) :
      c i * (Int.floor (x i + t i) : ℝ) - c i * (Int.floor (y i + t i) : ℝ) ≤
        (if i ∈ a then c i else 0) - (if i ∈ s then c i else 0) := by
    by_cases his : i ∈ s
    · have hci := hcross i his
      have horder : x i ≤ y i := hci.1.le.trans hci.2
      have hdiff : (Int.floor (y i + t i) : ℝ) -
          (Int.floor (x i + t i) : ℝ) = 1 := by
        exact_mod_cast (FloorCocycle.floor_sub_eq_one_iff
          (hx01 i).1 (hx01 i).2 (hy01 i).1 (hy01 i).2 horder (t i)).mpr hci
      simp only [ite_eq_left his]
      by_cases hia : i ∈ a
      · simp only [ite_eq_left hia]
        nlinarith [hc i]
      · simp only [ite_eq_right hia]
        nlinarith [hc i]
    · by_cases hia : i ∈ a
      · have hdiff : (Int.floor (x i + t i) : ℝ) -
            (Int.floor (y i + t i) : ℝ) ≤ 1 := by
          exact_mod_cast (FloorCocycle.floor_sub_bounds
            (hy01 i).1 (hy01 i).2 (hx01 i).1 (hx01 i).2 (t i)).2
        simp only [ite_eq_left hia, ite_eq_right his, sub_zero]
        have := mul_le_mul_of_nonneg_left hdiff (hc i)
        nlinarith
      · have hfloor : (Int.floor (x i + t i) : ℝ) ≤
            (Int.floor (y i + t i) : ℝ) := by
          apply Int.cast_le.mpr
          apply Int.floor_mono
          linarith [hxy i hia]
        simp only [ite_eq_right hia, ite_eq_right his, sub_self]
        exact sub_nonpos.mpr (mul_le_mul_of_nonneg_left hfloor (hc i))
  have hsum := (hsx.sub hsy).tsum_le_tsum hbound
    ((summable_finset_mask c a).sub (summable_finset_mask c s))
  rw [hsx.tsum_sub hsy, (summable_finset_mask c a).tsum_sub
    (summable_finset_mask c s), tsum_finset_mask, tsum_finset_mask] at hsum
  rw [← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  linarith

end Invariant233.InfiniteRatioCaps

namespace Invariant233.CircleWeights

theorem cocycle_ratio_cap_with_crossings {ι : Type*}
    (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (k : ℤ)
    (x y : UnitAddCircle) (a s : Finset ι)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, i ∉ a → coordinate q i x ≤ coordinate q i y)
    (hx : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)))
    (hy : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i y + (k : ℝ) * phase θ q i)))
    (hcross : ∀ i ∈ s, coordinate q i x < 1 - Int.fract ((k : ℝ) * phase θ q i) ∧
      1 - Int.fract ((k : ℝ) * phase θ q i) ≤ coordinate q i y) :
    cocycle θ q c k y / cocycle θ q c k x ≤
      Real.exp ((∑ i ∈ a, c i) - ∑ i ∈ s, c i) := by
  exact InfiniteRatioCaps.ratio_le_exp_exception_sub_crossings
    (fun i => coordinate q i x) (fun i => coordinate q i y)
    (fun i => (k : ℝ) * phase θ q i) c a s
    (fun i => coordinate_mem_Ico q i x) (fun i => coordinate_mem_Ico q i y)
    hc hxy hx hy hcross

theorem cocycle_ratio_cap_finite_exceptions {ι : Type*}
    (θ : ℝ) (q : ι → ℤ) (c : ι → ℝ) (k : ℤ)
    (x y : UnitAddCircle) (a : Finset ι)
    (hc : ∀ i, 0 ≤ c i)
    (hxy : ∀ i, i ∉ a → coordinate q i x ≤ coordinate q i y)
    (hx : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i x + (k : ℝ) * phase θ q i)))
    (hy : HasFiniteSupport (fun i =>
      Int.floor (coordinate q i y + (k : ℝ) * phase θ q i))) :
    cocycle θ q c k y / cocycle θ q c k x ≤ Real.exp (∑ i ∈ a, c i) := by
  simpa only [Finset.sum_empty, sub_zero] using
    cocycle_ratio_cap_with_crossings θ q c k x y a ∅ hc hxy hx hy
      (by intro i hi; simp at hi)

end Invariant233.CircleWeights

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_L2UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Invariant233.EndpointLoss

variable {X ι : Type*} [MeasurableSpace X]

theorem uniformlyAbsolutelyContinuous_of_uniform_sqrt_bound
    (μ : Measure X) [IsFiniteMeasure μ] (ν : ι → Measure X)
    (hfinite : ∀ i, IsFiniteMeasure (ν i)) (H : ℝ)
    (hbound : ∀ i A, MeasurableSet A → (ν i).real A ≤ H * Real.sqrt (μ.real A)) :
    UniformlyAbsolutelyContinuous μ ν := by
  intro ε hε
  have he : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hB : 0 < |H| + 1 := by positivity
  have hd : 0 < (ε : ℝ) / (|H| + 1) := div_pos he hB
  refine ⟨⟨((ε : ℝ) / (|H| + 1)) ^ 2, sq_nonneg _⟩, ?_, ?_⟩
  · change 0 < ((ε : ℝ) / (|H| + 1)) ^ 2
    positivity
  · intro A hA hsmall i
    let := hfinite i
    have hreal : μ.real A < ((ε : ℝ) / (|H| + 1)) ^ 2 := by
      exact (ENNReal.toReal_lt_toReal (measure_ne_top μ A) ENNReal.coe_ne_top).2 hsmall
    have hsqrt : Real.sqrt (μ.real A) < (ε : ℝ) / (|H| + 1) := by
      have ht := Real.sqrt_lt_sqrt (measureReal_nonneg) hreal
      simpa only [Real.sqrt_sq hd.le] using ht
    have hH : H ≤ |H| + 1 := by linarith [le_abs_self H]
    have hν : (ν i).real A < (ε : ℝ) := calc
      (ν i).real A ≤ H * Real.sqrt (μ.real A) := hbound i A hA
      _ ≤ (|H| + 1) * Real.sqrt (μ.real A) :=
        mul_le_mul_of_nonneg_right hH (Real.sqrt_nonneg _)
      _ < (|H| + 1) * ((ε : ℝ) / (|H| + 1)) :=
        mul_lt_mul_of_pos_left hsqrt hB
      _ = (ε : ℝ) := mul_div_cancel₀ _ hB.ne'
    exact (ENNReal.toReal_lt_toReal (measure_ne_top (ν i) A) ENNReal.coe_ne_top).1 hν

theorem uniformlyAbsolutelyContinuous_withDensity
    (μ : Measure X) [IsFiniteMeasure μ] (h : ι → X → ℝ)
    (hh : ∀ i, MemLp (h i) 2 μ) (hn : ∀ i, 0 ≤ᵐ[μ] h i) (H : ℝ)
    (hb : ∀ i, Real.sqrt (∫ x, h i x ^ 2 ∂μ) ≤ H) :
    UniformlyAbsolutelyContinuous μ
      (fun i => μ.withDensity (fun x => ENNReal.ofReal (h i x))) := by
  have hfin : ∀ i, IsFiniteMeasure (μ.withDensity (fun x => ENNReal.ofReal (h i x))) :=
    fun i => isFiniteMeasure_withDensity_ofReal ((hh i).integrable (by norm_num)).2
  apply uniformlyAbsolutelyContinuous_of_uniform_sqrt_bound μ _ hfin H
  intro i A hA
  exact (withDensity_measureReal_le_sqrt μ (hh i) (hn i) hA).trans
    (mul_le_mul_of_nonneg_right (hb i) (Real.sqrt_nonneg _))

end Invariant233.EndpointLoss

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

theorem orbit_inclusion (W : Aˣ) (D : A)
    (h : (1 - p) * ((W : A) * D) * p = 0) :
    (1 - (↑(W⁻¹) * p * (W : A))) * D * p = 0 := by
  have heq : ↑(W⁻¹) * ((1 - p) * ((W : A) * D) * p) =
      (1 - (↑(W⁻¹) * p * (W : A))) * D * p := by
    simp only [mul_sub, sub_mul, one_mul, mul_assoc]
    simp
  rw [← heq, h, mul_zero]

theorem orbit_inclusion_pow (hp : IsIdempotentElem p)
    (hT : (1 - p) * T * p = 0) (n : ℕ) (W : Aˣ) (D : A)
    (hfactor : T ^ n = (W : A) * D) :
    (1 - (↑(W⁻¹) * p * (W : A))) * D * p = 0 := by
  apply orbit_inclusion W D
  rw [← hfactor]
  exact invariant_pow hp hT n

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
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
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

theorem scalar_multiplier_fields_complete (b : HilbertBasis ι ℂ E)
    (A : Lp E 2 μ →L[ℂ] Lp E 2 μ)
    (hA : ∀ g : Lp ℂ ∞ μ, Commute A (multiplier g)) :
    ∃ F : X → E →L[ℂ] E,
      (∀ x, ‖F x‖ ≤ ‖A‖) ∧
      (∀ v : E, StronglyMeasurable fun x => F x v) ∧
      (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => F x (f x)) ∧
      (∀ G : X → E →L[ℂ] E,
        (∀ f : Lp E 2 μ, A f =ᵐ[μ] fun x => G x (f x)) → F =ᵐ[μ] G) ∧
      (∀ f : Lp E 2 μ, A.adjoint f =ᵐ[μ] fun x => (F x).adjoint (f x)) ∧
      (∀ (B : Lp E 2 μ →L[ℂ] Lp E 2 μ) (G : X → E →L[ℂ] E),
        (∀ f : Lp E 2 μ, B f =ᵐ[μ] fun x => G x (f x)) →
        ∀ f : Lp E 2 μ, (A * B) f =ᵐ[μ] fun x => (F x * G x) (f x)) ∧
      (IsStarProjection A → ∀ᵐ x ∂μ, IsStarProjection (F x)) := by
  let := separableSpace_of_countable_hilbertBasis b
  obtain ⟨F, hnorm, hmeas, hrep, huniq⟩ := exists_unique_field_of_commutes b A hA
  have hAT : A = DirectIntegral.fieldOperator F ‖A‖ hnorm
      (fun v => (hmeas v).aestronglyMeasurable) := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hrep f).trans (DirectIntegral.fieldOperatorVec_ae F ‖A‖ hnorm
      (fun v => (hmeas v).aestronglyMeasurable) f).symm
  refine ⟨F, hnorm, hmeas, hrep, huniq, ?_, ?_, ?_⟩
  · have hnormAdj : ∀ x, ‖(F x).adjoint‖ ≤ ‖A‖ := by
      intro x
      simpa only [LinearIsometryEquiv.norm_map] using hnorm x
    have hmeasAdj : ∀ v, AEStronglyMeasurable (fun x => (F x).adjoint v) μ := by
      intro v
      exact (StrongField.stronglyMeasurable_adjoint_apply_of_columns b F
        (fun i => hmeas (b i)) v).aestronglyMeasurable
    have hAdj : DirectIntegral.fieldOperator (fun x => (F x).adjoint) ‖A‖ hnormAdj hmeasAdj =
        A.adjoint := by
      calc
        _ = (DirectIntegral.fieldOperator F ‖A‖ hnorm
            (fun v => (hmeas v).aestronglyMeasurable)).adjoint :=
          DirectIntegral.fieldOperator_adjoint_of_ae_eq
            (Filter.Eventually.of_forall fun x => rfl)
        _ = A.adjoint := congrArg ContinuousLinearMap.adjoint hAT.symm
    intro f
    rw [← hAdj]
    exact DirectIntegral.fieldOperator_ae _ _ _ _ f
  · intro B G hG f
    filter_upwards [hrep (B f), hG f] with x hx hy
    change A (B f) x = (F x) (G x (f x))
    rw [hx, hy]
  · intro hP
    have hPT : IsStarProjection (DirectIntegral.fieldOperator (μ := μ) F ‖A‖ hnorm
        (fun v => (hmeas v).aestronglyMeasurable)) := by
      rw [← hAT]
      exact hP
    exact DirectIntegral.ae_isStarProjection_of_fieldOperator b (norm_nonneg A) hmeas hPT

end Invariant233.L2Multiplication

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

private theorem blocksWithZero_partition :
    ∀ i : ℕ, ∃! j : ℕ, i ∈ blocksWithZero p j := by
  intro i
  by_cases hi : i = 0
  · subst i
    refine ⟨0, by simp [blocksWithZero], ?_⟩
    intro j hj
    by_contra h
    have hb : 0 ∈ p.block j := by simpa [blocksWithZero, h] using hj
    have hb' := (p.mem_block_iff j 0).mp hb
    omega
  · obtain ⟨j, hj, hij⟩ := p.exists_mem_block hp.m_pos i (by omega)
    have hj0 : j ≠ 0 := by omega
    refine ⟨j, by simpa [blocksWithZero, hj0] using hij, ?_⟩
    intro k hik
    have hk0 : k ≠ 0 := by
      intro hk
      subst k
      simp [blocksWithZero, hi] at hik
    have hk : i ∈ p.block k := by simpa [blocksWithZero, hk0] using hik
    exact p.block_index_unique hp.m_pos hk hij

theorem summable_phases_all : Summable (p.alpha θ) := by
  classical
  apply (summable_partition (fun i => Int.fract_nonneg _) hp.blocksWithZero_partition).mpr
  constructor
  · intro j
    exact (hasSum_fintype _).summable
  · apply (summable_nat_add_iff 1).mp
    apply hp.summable_block_phases.congr
    intro n
    simp only [blocksWithZero,
      tsum_fintype, CircleParameterData.alpha]
    exact (Finset.sum_attach (p.block (n + 1)) (fun i => Int.fract ((p.q i : ℝ) * θ))).symm

theorem summable_phases : Summable (fun i : ℕ => p.alpha θ (i + 1)) :=
  (summable_nat_add_iff 1).mpr hp.summable_phases_all

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

theorem operator_pow_apply (w : Weight) (n : ℕ) (ξ : Hilbert) (k : ℤ) :
    (((operator w)^n) ξ) k =
      (∏ j ∈ Finset.range n, w (k - n + j)) * ξ (k - n) := by
  simpa using operator_pow_apply_add w n ξ (k - n)

theorem operator_pow_eq_shift_diagonal (w : Weight) (n : ℕ) :
    (operator w)^n =
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap.comp
        (diagonal (orbitProduct w n)) := by
  ext ξ k
  exact operator_pow_apply w n ξ k

end Invariant233.WeightedShift

end

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongFieldContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace InvariantProjection

open Filter Topology

variable {𝕜 E F G ι X : Type*}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable [TopologicalSpace X]

theorem strong_continuous_of_dense_of_bounded
    {A : X → E →L[𝕜] F} {s : Set E} {C : ℝ}
    (hs : Dense s) (hA : ∀ w ∈ s, Continuous (fun x => A x w))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => A x v) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_uniformity_dist.mp hu
  let M : ℝ := max C 0 + 1
  have hM : 0 < M := by dsimp [M] <;> positivity
  obtain ⟨w, hw, hvw⟩ := hs.exists_dist_lt v (div_pos hε hM)
  refine ⟨(fun x => A x w), hA w hw, ?_⟩
  intro x
  apply hsub
  calc
    dist (A x v) (A x w) ≤ ‖A x‖ * dist v w := (A x).dist_le_opNorm v w
    _ ≤ M * dist v w := mul_le_mul_of_nonneg_right
      ((hC x).trans ((le_max_left C 0).trans (by dsimp [M]; exact le_add_of_nonneg_right zero_le_one)))
      (dist_nonneg)
    _ < ε := by simpa [mul_comm] using (lt_div_iff₀ hM).mp hvw

theorem strong_continuous_of_dense_span_of_bounded
    {A : X → E →L[𝕜] F} {b : ι → E} {C : ℝ}
    (hb : Dense (Submodule.span 𝕜 (Set.range b) : Set E))
    (hA : ∀ i, Continuous (fun x => A x (b i)))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => A x v) := by
  apply strong_continuous_of_dense_of_bounded hb ?_ hC v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hA i
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  | add w z hw hz ihw ihz =>
      have h : Continuous (fun x => A x w + A x z) :=
        Continuous.add (f := fun x => A x w) (g := fun x => A x z) ihw ihz
      simpa only [map_add] using h
  | smul c w hw ihw =>
      have h : Continuous (fun x => c • A x w) :=
        Continuous.const_smul (g := fun x => A x w) ihw c
      simpa only [map_smul] using h

theorem strong_continuous_comp_of_bounded
    {A : X → F →L[𝕜] G} {B : X → E →L[𝕜] F} {C : ℝ}
    (hA : ∀ w, Continuous (fun x => A x w))
    (hB : ∀ v, Continuous (fun x => B x v))
    (hC : ∀ x, ‖A x‖ ≤ C) (v : E) :
    Continuous (fun x => ((A x).comp (B x)) v) := by
  exact continuous_apply_of_strong_continuous_of_bounded
    (A := A) (v := fun x => B x v) hA hC (hB v)

theorem isClosed_zero_set_of_strong_continuous
    {A : X → E →L[𝕜] F}
    (hA : ∀ v, Continuous (fun x => A x v)) :
    IsClosed {x | A x = 0} := by
  have heq : {x | A x = 0} = ⋂ v : E, {x | A x v = 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hx v
      simp [hx]
    · intro hx
      ext v
      exact hx v
  rw [heq]
  exact isClosed_iInter fun v => isClosed_eq (hA v) continuous_const

end InvariantProjection

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_DiagonalContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.sequenceHilbertIntBorelSpace _root_.OAI.Invariant233.sequenceHilbertIntMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped ENNReal lp

namespace Invariant233.SequenceHilbert

variable {I X : Type*}

theorem norm_diagonal_le (a : I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ i, ‖a i‖ ≤ C) : ‖diagonal a C hC ha‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

theorem diagonal_congr (a b : I → ℂ) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ i, ‖a i‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ D)
    (hab : ∀ i, a i = b i) : diagonal a C hC ha = diagonal b D hD hb := by
  ext v i
  simp only [diagonal_apply, hab]

theorem strong_continuous_diagonal [TopologicalSpace X]
    (a : X → I → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ x i, ‖a x i‖ ≤ C)
    (hc : ∀ i, Continuous (fun x => a x i)) (v : SequenceHilbert I) :
    Continuous (fun x => diagonal (a x) C hC (ha x) v) := by
  classical
  let b : HilbertBasis I ℂ (SequenceHilbert I) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : ∀ i, b i = lp.single 2 i (1 : ℂ) := fun _ => rfl
  apply InvariantProjection.strong_continuous_of_dense_span_of_bounded
    (b := b) (C := C)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span) ?_
    (fun x => norm_diagonal_le (a x) C hC (ha x)) v
  intro i
  simpa only [hb, diagonal_single, mul_one, Function.comp_def,
    lp.singleContinuousLinearMap_apply] using
    (lp.singleContinuousLinearMap ℂ (fun _ : I => ℂ) 2 i).continuous.comp (hc i)

end Invariant233.SequenceHilbert

namespace Invariant233

variable {I X : Type*} [TopologicalSpace X]

theorem isClosed_diagonal_relation
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, Continuous (fun x => p x v))
    (hdc : ∀ i, Continuous (fun t => d t i))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsClosed {t : X × X |
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} := by
  apply InvariantProjection.isClosed_zero_set_of_strong_continuous
  intro v
  have hleft : ∀ w, Continuous (fun t : X × X => (1 - p t.2) w) := by
    intro w
    have h : Continuous (fun t : X × X => w - p t.2 w) :=
      continuous_const.sub ((hp w).comp continuous_snd)
    simpa using h
  have hleftn : ∀ t : X × X,
      ‖1 - p t.2‖ ≤ ‖(1 : SequenceHilbert I →L[ℂ] SequenceHilbert I)‖ + C := by
    intro t
    exact (norm_sub_le _ _).trans (add_le_add le_rfl (hpn t.2))
  have hright : ∀ w, Continuous (fun t : X × X =>
      ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) w) := by
    intro w
    apply InvariantProjection.strong_continuous_comp_of_bounded
      (fun z => SequenceHilbert.strong_continuous_diagonal d B hB hd hdc z)
      (fun z => (hp z).comp continuous_fst)
      (fun t => SequenceHilbert.norm_diagonal_le (d t) B hB (hd t)) w
  exact InvariantProjection.strong_continuous_comp_of_bounded hleft hright hleftn v

theorem isCompact_diagonal_relation [CompactSpace X]
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, Continuous (fun x => p x v))
    (hdc : ∀ i, Continuous (fun t => d t i))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsCompact {t : X × X |
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} :=
  (isClosed_diagonal_relation p d B C hB hd hp hdc hpn).isCompact

theorem isCompact_diagonal_relation_on
    (Q : Set X) (hQ : IsCompact Q)
    (p : X → SequenceHilbert I →L[ℂ] SequenceHilbert I)
    (d : (X × X) → I → ℂ) (B C : ℝ) (hB : 0 ≤ B)
    (hd : ∀ t i, ‖d t i‖ ≤ B)
    (hp : ∀ v, ContinuousOn (fun x => p x v) Q)
    (hdc : ∀ i, ContinuousOn (fun t => d t i) (Q ×ˢ Q))
    (hpn : ∀ x, ‖p x‖ ≤ C) :
    IsCompact {t : X × X | t ∈ Q ×ˢ Q ∧
      (1 - p t.2).comp ((SequenceHilbert.diagonal (d t) B hB (hd t)).comp (p t.1)) = 0} := by
  let : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let f : Q × Q → X × X := fun t => ((t.1 : X), (t.2 : X))
  have hf : Continuous f :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  let pQ : Q → SequenceHilbert I →L[ℂ] SequenceHilbert I := fun x => p x
  let dQ : (Q × Q) → I → ℂ := fun t => d (f t)
  have hpQ : ∀ v, Continuous (fun x : Q => pQ x v) := fun v => (hp v).domRestrict
  have hdQ : ∀ i, Continuous (fun t : Q × Q => dQ t i) := by
    intro i
    exact (hdc i).comp_continuous hf (fun t => ⟨t.1.property, t.2.property⟩)
  have hS := isCompact_diagonal_relation pQ dQ B C hB
    (fun t i => hd (f t) i) hpQ hdQ (fun x => hpn x)
  have himage := hS.image hf
  convert himage using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  constructor
  · rintro ⟨ht, hzero⟩
    refine ⟨(⟨t.1, ht.1⟩, ⟨t.2, ht.2⟩), ?_, rfl⟩
    exact hzero
  · rintro ⟨q, hzero, rfl⟩
    exact ⟨⟨q.1.property, q.2.property⟩, hzero⟩

end Invariant233

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

theorem boundedDiagonal_congr {a b : I → ℂ} (h : ∀ i, a i = b i) :
    boundedDiagonal a = boundedDiagonal b := by
  exact congrArg boundedDiagonal (funext h)

end Invariant233.SequenceHilbert

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedOrbitInvariance
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.WeightedShift.diagonalAlgHom_apply _root_.OAI.Invariant233.WeightedShift.diagonal_add _root_.OAI.Invariant233.WeightedShift.diagonal_mul _root_.OAI.Invariant233.WeightedShift.diagonal_one _root_.OAI.Invariant233.WeightedShift.diagonal_smul _root_.OAI.Invariant233.WeightedShift.diagonal_star _root_.OAI.Invariant233.WeightedShift.diagonal_zero _root_.OAI.Invariant233.WeightedShift.shift_zero _root_.OAI.Invariant233.WeightedShift.translate_add _root_.OAI.Invariant233.WeightedShift.translate_apply _root_.OAI.Invariant233.WeightedShift.translate_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace Invariant233.OrbitInvariance
open WeightedShift

theorem weighted_shift_orbit_inclusion (w : Weight) {p : Hilbert →L[ℂ] Hilbert}
    (hp : IsIdempotentElem p) (hT : (1 - p) * operator w * p = 0) (n : ℕ) :
    (1 - (shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * p *
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap) *
      diagonal (orbitProduct w n) * p = 0 := by
  exact orbit_inclusion_pow hp hT n (shiftUnit n) (diagonal (orbitProduct w n))
    (operator_pow_eq_shift_diagonal w n)

theorem diagonal_smul (c : ℂ) (w : Weight) :
    diagonal (c • w) = c • diagonal w := by
  ext ξ k
  simp [diagonal_apply, mul_assoc]

theorem weighted_shift_orbit_normalized (w : Weight) {p : Hilbert →L[ℂ] Hilbert}
    (hp : IsIdempotentElem p) (hT : (1 - p) * operator w * p = 0)
    (n : ℕ) (c : ℂ) :
    (1 - (shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * p *
      (shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap) *
      diagonal (c⁻¹ • orbitProduct w n) * p = 0 := by
  rw [diagonal_smul, mul_smul_comm, smul_mul_assoc,
    weighted_shift_orbit_inclusion w hp hT n, smul_zero]

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

theorem normalized_orbitProduct_eq_ratio {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    {x : Circle} (hx : x ∈ s) (n : ℕ) (v : ℤ) :
    ((p.floorCocycle θ (n : ℤ) x : ℂ)⁻¹ •
      WeightedShift.orbitProduct (hp.parameterOrbitWeight x) n) v =
      ((p.floorCocycle θ v (Rotation.action θ (n : ℤ) x) /
        p.floorCocycle θ v x : ℝ) : ℂ) := by
  have hpord : WeightedShift.orbitProduct (hp.parameterOrbitWeight x) n v =
      (p.floorCocycle θ (n : ℤ) (Rotation.action θ v x) : ℂ) := by
    rw [WeightedShift.orbitProduct_apply]
    have hprod := p.weight_product_eq_floorCocycle θ (Rotation.action θ v x)
      (hc _ ((hinv v x).mpr hx)) n
    convert hprod using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.prod_congr rfl
    intro j hj
    change (p.measurableWeight θ (Rotation.action θ (v + j) x) : ℂ) =
      (p.measurableWeight θ (Rotation.action θ (j : ℤ) (Rotation.action θ v x)) : ℂ)
    rw [Rotation.action_add, add_comm v]
  have hratio := CircleWeights.orbit_ratio_of_cocycle_identities θ
    p.coordFrequency p.coordCost x v (n : ℤ) (hc x hx v n) (hc x hx n v)
  change p.floorCocycle θ (n : ℤ) (Rotation.action θ v x) / p.floorCocycle θ (n : ℤ) x =
    p.floorCocycle θ v (Rotation.action θ (n : ℤ) x) / p.floorCocycle θ v x at hratio
  change (p.floorCocycle θ (n : ℤ) x : ℂ)⁻¹ *
    WeightedShift.orbitProduct (hp.parameterOrbitWeight x) n v = _
  rw [hpord, ← hratio, Complex.ofReal_div]
  simp only [div_eq_mul_inv, mul_comm]

theorem positive_orbit_identity_of_fiber {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    (P : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    {x : Circle} (hx : x ∈ s) (hP : IsIdempotentElem (P x))
    (hT : (1 - P x) * WeightedShift.operator (hp.parameterOrbitWeight x) * P x = 0)
    (n : ℕ)
    (hcov : P (Rotation.action θ (n : ℤ) x) =
      (WeightedShift.shift (-(n : ℤ))).toLinearIsometry.toContinuousLinearMap * P x *
        (WeightedShift.shift (n : ℤ)).toLinearIsometry.toContinuousLinearMap) :
    (1 - P (Rotation.action θ (n : ℤ) x)) *
      ratioDiagonal (p.floorCocycle θ) (x, Rotation.action θ (n : ℤ) x) * P x = 0 := by
  let w : Weight := (p.floorCocycle θ (n : ℤ) x : ℂ)⁻¹ •
    WeightedShift.orbitProduct (hp.parameterOrbitWeight x) n
  have hd : ratioDiagonal (p.floorCocycle θ) (x, Rotation.action θ (n : ℤ) x) =
      WeightedShift.diagonal w := by
    unfold ratioDiagonal
    rw [SequenceHilbert.boundedDiagonal_congr
      (fun v => (hp.normalized_orbitProduct_eq_ratio hinv hc hx n v).symm)]
    exact SequenceHilbert.boundedDiagonal_eq_weighted w
  rw [hd, hcov]
  exact OrbitInvariance.weighted_shift_orbit_normalized
    (hp.parameterOrbitWeight x) hP hT n (p.floorCocycle θ (n : ℤ) x : ℂ)

end CircleParameterLaws
end Invariant233

namespace Invariant233.Rotation

theorem ae_field_conjugation_of_mem_algebra {θ : ℝ}
    {P : Hilbert →L[ℂ] Hilbert} (hP : P ∈ algebra θ)
    (F : Circle → Fiber →L[ℂ] Fiber)
    (hrep : ∀ ξ : Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ, F (action θ k x) =
      (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap * F x *
        (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap := by
  apply ae_all_iff.mpr
  intro k
  have hc := DirectIntegral.ae_covariance_of_represented_commute
    (default : HilbertBasis ℤ ℂ Fiber) P F
    (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap
    (action θ k) (action_measurePreserving θ k) hrep
    (algebra_commutes_shiftedPullback_int_independent θ k hP)
  have hS : (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap *
      (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap = 1 := by
    ext ξ i
    simp [WeightedShift.shift_apply]
  filter_upwards [hc] with x hx
  calc
    F (action θ k x) = 1 * F (action θ k x) := (one_mul _).symm
    _ = ((WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap *
        (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap) *
          F (action θ k x) := by rw [hS]
    _ = (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap *
        ((WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap *
          F (action θ k x)) := mul_assoc _ _ _
    _ = (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap *
        (F x * (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap) := by rw [hx]
    _ = _ := (mul_assoc _ _ _).symm

theorem exists_projection_field {θ : ℝ} {P : Hilbert →L[ℂ] Hilbert}
    (hmem : P ∈ algebra θ) (hP : IsStarProjection P) :
    ∃ F : Circle → Fiber →L[ℂ] Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      (∀ᵐ x ∂circleMeasure, ∀ k : ℤ, F (action θ k x) =
        (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap) := by
  classical
  obtain ⟨G, hnorm, hmeas, hrep, _, _, _, hproj⟩ :=
    L2Multiplication.scalar_multiplier_fields_complete
      (default : HilbertBasis ℤ ℂ Fiber) P (algebra_commutes_multiplier θ hmem)
  obtain ⟨N, hsub, hN, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp (hproj hP))
  let F : Circle → Fiber →L[ℂ] Fiber := fun x => if x ∈ N then 0 else G x
  have hgood : ∀ x, x ∉ N → IsStarProjection (G x) := by
    intro x hx
    by_contra h
    exact hx (hsub h)
  have hnotN : ∀ᵐ x ∂circleMeasure, x ∉ N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hNzero
  have heq : F =ᵐ[circleMeasure] G := by
    filter_upwards [hnotN] with x hx
    simp only [F, ite_eq_right hx]
  have hFrep : ∀ ξ : Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x) := by
    intro ξ
    filter_upwards [hrep ξ, heq] with x hx hg
    rw [hg]
    exact hx
  refine ⟨F, ?_, ?_, ?_, hFrep,
    ae_field_conjugation_of_mem_algebra hmem F hFrep⟩
  · intro x
    by_cases hx : x ∈ N
    · simp only [F, ite_eq_left hx]
      exact IsStarProjection.zero _
    · simpa only [F, ite_eq_right hx] using hgood x hx
  · intro x
    by_cases hx : x ∈ N
    · simpa only [F, ite_eq_left hx, norm_zero] using norm_nonneg P
    · simpa only [F, ite_eq_right hx] using hnorm x
  · intro v
    have he : (fun x => F x v) = N.piecewise (fun _ => (0 : Fiber)) (fun x => G x v) := by
      funext x
      by_cases hx : x ∈ N <;> simp [F, hx, Set.piecewise]
    rw [he]
    exact stronglyMeasurable_const.piecewise hN (hmeas v)

end Invariant233.Rotation

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem exists_measurableOperator_positive_orbit_field
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      (∀ᵐ x ∂circleMeasure, ∀ k : ℤ, F (Rotation.action θ k x) =
        (WeightedShift.shift (-k)).toLinearIsometry.toContinuousLinearMap * F x *
          (WeightedShift.shift k).toLinearIsometry.toContinuousLinearMap) ∧
      (∀ᵐ x ∂circleMeasure, ∀ n : ℕ,
        (1 - F (Rotation.action θ (n : ℤ) x)) *
          ratioDiagonal (p.floorCocycle θ) (x, Rotation.action θ (n : ℤ) x) * F x = 0) := by
  obtain ⟨F, hproj, hnorm, hmeas, hrep, hcov⟩ := Rotation.exists_projection_field hmem hP
  have hinv := DirectIntegral.ae_invariant_of_representations
    (default : HilbertBasis ℤ ℂ Rotation.Fiber) P (p.measurableOperator θ hp) F
    (fun x => WeightedShift.operator (hp.parameterOrbitWeight x)) hrep
    hp.measurableOperator_ae hT
  obtain ⟨s, _, hfull, hs, _, hc⟩ := hp.exists_parameter_cocycle_set
  refine ⟨F, hproj, hnorm, hmeas, hrep, hcov, ?_⟩
  filter_upwards [hinv, hcov, hfull] with x hix hcx hsx
  intro n
  exact hp.positive_orbit_identity_of_fiber hs hc F hsx (hproj x).isIdempotentElem
    hix n (hcx n)

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CirclePhaseTails
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter
open scoped BigOperators Topology

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem early_trimming_bound (j : ℕ) :
    (p.blockEnd (j - 1) : ℝ) * (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j ≤
      1 / ((j + 1 : ℕ) : ℝ)^2 := by
  have hq : 0 < (p.q (p.blockEnd (j - 1)) : ℝ) := by
    exact_mod_cast hp.q_pos (p.blockEnd (j - 1))
  have ha : 0 ≤ (p.blockEnd (j - 1) : ℝ) := Nat.cast_nonneg _
  have hr : (p.blockEnd (j - 1) : ℝ) / (1 + (p.blockEnd (j - 1) : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  calc
    _ = ((p.blockEnd (j - 1) : ℝ) / (1 + (p.blockEnd (j - 1) : ℝ))) *
        (1 / ((j + 1 : ℕ) : ℝ)^2) := by
      unfold CircleParameterData.ell
      field_simp
    _ ≤ 1 * (1 / ((j + 1 : ℕ) : ℝ)^2) :=
      mul_le_mul_of_nonneg_right hr (by positivity)
    _ = _ := one_mul _

theorem discarded_mass_bound (j : ℕ) (hj : 1 ≤ j) :
    (p.blockEnd (j - 1) : ℝ) * (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j +
      2 * p.Q j * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ)) ≤
      1 / ((j + 1 : ℕ) : ℝ)^2 + 4 * p.Q j / (p.K (j + 1) : ℝ) := by
  apply add_le_add (hp.early_trimming_bound j)
  have hQ : 0 ≤ p.Q j := Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc
    _ ≤ 2 * p.Q j * (2 / (p.K (j + 1) : ℝ)) :=
      mul_le_mul_of_nonneg_left (hp.reciprocal_tail_bound j hj) (by positivity)
    _ = _ := by ring

theorem tendsto_discarded_mass_bound :
    Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)^2 +
      4 * p.Q (n + 1) / (p.K (n + 2) : ℝ)) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    exact (tendsto_add_atTop_iff_nat 2).mpr tendsto_one_div_atTop_nhds_zero_nat
  have hsq : Tendsto (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)^2)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div_pow, zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  have hg := hsq.add (hp.tendsto_sampling_horizon.const_mul 4)
  simpa only [mul_div_assoc, zero_add, mul_zero] using hg

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RationalGraphTrimming
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
namespace Invariant233.CircleParameterData

theorem coordinate_mem_Ico (p : CircleParameterData) (i : ℕ) (x : Circle) :
    p.coordinate i x ∈ Set.Ico (0 : ℝ) 1 := by
  simpa only [coordinate, rep, zero_add] using
    (AddCircle.equivIco (1 : ℝ) 0 (p.q i • x)).property

theorem coordinate_orbit (p : CircleParameterData) (θ : ℝ) (i n : ℕ)
    (x : Circle) :
    p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) =
      Int.fract (p.coordinate i x + (n : ℝ) * p.alpha θ i) := by
  simpa only [coordinate, rep, alpha, Int.cast_natCast, natCast_zsmul,
    ← AddCircle.coe_nsmul, nsmul_eq_mul] using
    CircleCharacterDynamics.character_orbit_representative (p.q i : ℤ) (n : ℤ) θ x

theorem kernel_ne_zero_support {m : ℕ} {z v : ℝ} (h : kernel m z v ≠ 0) :
    1 / (m : ℝ)^2 ≤ delta z ∧ 0 < v ∧ v < kernelWidth m * delta z := by
  unfold kernel at h
  split_ifs at h with hs
  · exact hs
  · exact (h rfl).elim

theorem kernel_no_wrap {m : ℕ} (hm : 1 ≤ m) {z v : ℝ}
    (hz : z ∈ Set.Ico (0 : ℝ) 1) (hk : kernel m z v ≠ 0) :
    0 < v ∧ z + v < 1 := by
  have hs := kernel_ne_zero_support hk
  have hw : kernelWidth m ≤ 1 := by
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hm) (by norm_num)
  have hd : 0 ≤ delta z := by
    unfold delta
    exact le_min (Int.fract_nonneg z) (by linarith [Int.fract_lt_one z])
  have hd' : delta z ≤ 1 - z := by
    unfold delta
    rw [Int.fract_eq_self.mpr hz]
    exact min_le_right _ _
  have hv : v < delta z := hs.2.2.trans_le (by nlinarith)
  exact ⟨hs.2.1, by linarith⟩

theorem current_block_ordered (p : CircleParameterData) (θ : ℝ) (j n : ℕ)
    (hm : 1 ≤ p.m j) (x : Circle) (hd : p.orbitGraphDensity θ j n x ≠ 0)
    {i : ℕ} (hi : i ∈ p.block j) :
    p.coordinate i x ≤ p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  have hk : kernel (p.m j) (p.coordinate i x)
      (Int.fract ((n : ℝ) * p.alpha θ i)) ≠ 0 := by
    exact (Finset.prod_ne_zero_iff.mp hd) i hi
  obtain ⟨hv, hsum⟩ := kernel_no_wrap hm (p.coordinate_mem_Ico i x) hk
  rw [p.coordinate_orbit]
  have he : Int.fract (p.coordinate i x + (n : ℝ) * p.alpha θ i) =
      Int.fract (p.coordinate i x + Int.fract ((n : ℝ) * p.alpha θ i)) := by
    conv_lhs => rw [← Int.fract_add_floor ((n : ℝ) * p.alpha θ i)]
    rw [← add_assoc, Int.fract_add_intCast]
  rw [he, Int.fract_eq_self.mpr
    ⟨by linarith [(p.coordinate_mem_Ico i x).1], hsum⟩]
  linarith

theorem measurableSet_rationalGraphGood (p : CircleParameterData) (A j : ℕ) :
    MeasurableSet (p.rationalGraphGood A j) := by
  unfold rationalGraphGood
  simp only [Set.ofPred_and, Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => measurableSet_lt (p.measurable_coordinate i) measurable_const
  · exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
        measurableSet_lt (p.measurable_coordinate i) measurable_const

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem trimming_coordinate_rational_translation {A i : ℕ} (hAi : A ≤ i)
    (r : ℤ) (x : Circle) :
    p.coordinate i (x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle)) =
      p.coordinate i x := by
  simpa only [coordinate, rep, Int.cast_natCast, natCast_zsmul] using
    CircleCharacterDynamics.character_rational_translation
      (q := (p.q i : ℤ)) (d := (p.q A : ℤ))
      (by exact_mod_cast (hp.q_pos A).ne')
      (by exact_mod_cast hp.trimming_frequency_dvd_of_le hAi) r x

theorem early_coordinate_ordered {A j i n : ℕ} (hAi : A ≤ i)
    (hia : i ≤ p.blockEnd (j - 1)) (x : Circle)
    (hx : x ∈ p.rationalGraphGood A j) (t : ℝ)
    (ht : p.q A • (t : Circle) = 0)
    (hn : Int.fract ((n : ℝ) * θ - t) < p.ell j) :
    p.coordinate i x ≤ p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  let δ : ℝ := Int.fract ((n : ℝ) * θ - t)
  have hδ : 0 ≤ δ := Int.fract_nonneg _
  have hqi : 0 ≤ (p.q i : ℝ) := Nat.cast_nonneg _
  have hqa : (p.q i : ℝ) ≤ p.q (p.blockEnd (j - 1)) := by
    exact_mod_cast hp.frequency_increasing.monotone hia
  have hell : 0 < p.ell j := by
    unfold ell
    have hq : (0 : ℝ) < p.q (p.blockEnd (j - 1)) := by
      exact_mod_cast hp.q_pos _
    positivity
  have hmove : (p.q i : ℝ) * δ ≤ (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j := by
    exact mul_le_mul hqa hn.le hδ (Nat.cast_nonneg _)
  have hnowrap : p.coordinate i x + (p.q i : ℝ) * δ < 1 := by
    have htrim := hx.1 i hAi hia
    linarith
  have hti : p.q i • (t : Circle) = 0 := by
    obtain ⟨k, hk⟩ := hp.trimming_frequency_dvd_of_le hAi
    rw [hk, mul_nsmul, ht, nsmul_zero]
  have he : (((n : ℝ) * θ : ℝ) : Circle) = (t : Circle) + (δ : Circle) := by
    dsimp [δ]
    rw [AddCircle.coe_fract, AddCircle.coe_sub]
    abel
  have hecoord : p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) =
      Int.fract (p.coordinate i x + (p.q i : ℝ) * δ) := by
    change rep (p.q i • (x + (((n : ℝ) * θ : ℝ) : Circle))) = _
    rw [he, nsmul_add, nsmul_add, hti, zero_add,
      ← AddCircle.coe_nsmul, nsmul_eq_mul]
    exact CircleCharacterDynamics.representative_add_real _ _
  rw [hecoord, Int.fract_eq_self.mpr ⟨add_nonneg (p.coordinate_mem_Ico i x).1
    (mul_nonneg hqi hδ), hnowrap⟩]
  exact le_add_of_nonneg_right (mul_nonneg hqi hδ)

theorem future_coordinate_ordered {A j s i n : ℕ} (hjs : j < s)
    (hi : i ∈ p.block s) (x : Circle) (hx : x ∈ p.rationalGraphGood A j)
    (hn : (n : ℝ) ≤ p.Q j) :
    p.coordinate i x ≤ p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  have hs : 1 ≤ s := by omega
  have hN : 0 < p.N s := mul_pos (by exact_mod_cast hp.m_pos s hs)
    (by exact_mod_cast hp.K_pos s hs)
  have hα := hp.phase_bounds s hs i hi
  have hmove : (n : ℝ) * p.alpha θ i ≤ 2 * p.Q j / p.N s := by
    calc
      _ ≤ p.Q j * (2 / p.N s) := mul_le_mul hn hα.2.le
        (one_div_pos.mpr hN |>.le.trans hα.1.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      _ = _ := by ring
  have hnowrap : p.coordinate i x + (n : ℝ) * p.alpha θ i < 1 := by
    have htrim := hx.2 s hjs i hi
    linarith
  have hmove0 : 0 ≤ (n : ℝ) * p.alpha θ i :=
    mul_nonneg (Nat.cast_nonneg _) ((one_div_pos.mpr hN).le.trans hα.1.le)
  rw [p.coordinate_orbit, Int.fract_eq_self.mpr
    ⟨add_nonneg (p.coordinate_mem_Ico i x).1 hmove0, hnowrap⟩]
  exact le_add_of_nonneg_right hmove0

theorem ordered_of_rationalGraphGood {A j n : ℕ} (hA : 1 ≤ A) (hj : 1 ≤ j)
    (x : Circle) (hx : x ∈ p.rationalGraphGood A j) (t : ℝ)
    (ht : p.q A • (t : Circle) = 0)
    (hphase : Int.fract ((n : ℝ) * θ - t) < p.ell j)
    (hn : (n : ℝ) ≤ p.Q j)
    (hd : p.orbitGraphDensity θ j n x ≠ 0) :
    ∀ i, A ≤ i → p.coordinate i x ≤
      p.coordinate i (x + (((n : ℝ) * θ : ℝ) : Circle)) := by
  intro i hAi
  by_cases hia : i ≤ p.blockEnd (j - 1)
  · exact hp.early_coordinate_ordered hAi hia x hx t ht hphase
  · by_cases hij : i ≤ p.blockEnd j
    · exact p.current_block_ordered θ j n (hp.m_pos j hj) x hd
        ((p.mem_block_iff j i).mpr ⟨by omega, hij⟩)
    · obtain ⟨s, hs, his⟩ := p.exists_mem_block hp.m_pos i (hA.trans hAi)
      have hjs : j < s := by
        by_contra h
        have hsj : s ≤ j := by omega
        have hb := (p.blockEnd_strictMono hp.m_pos).monotone hsj
        have hi := (p.mem_block_iff s i).mp his
        omega
      exact hp.future_coordinate_ordered hjs his x hx hn

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleFlattenedCosts
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Invariant233.CircleParameterLaws
open scoped BigOperators ENNReal
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem flattenedCost_pos (n : ℕ) : 0 < p.flattenedCost n := by
  exact hp.C_pos _ (p.blockIndex_pos hp.m_pos (by omega))

end Invariant233.CircleParameterLaws

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
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RationalGraphRatioCaps
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Function Set
open scoped BigOperators
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem floorCocycle_ratio_le_prefix {A : ℕ} (hA : 1 ≤ A) (x y : Circle) (v : ℤ)
    (hxy : ∀ i, A ≤ i → p.coordinate i x ≤ p.coordinate i y)
    (hx : HasFiniteSupport (fun k : ℕ =>
      Int.floor (p.coordinate (k + 1) x + (v : ℝ) * p.alpha θ (k + 1))))
    (hy : HasFiniteSupport (fun k : ℕ =>
      Int.floor (p.coordinate (k + 1) y + (v : ℝ) * p.alpha θ (k + 1)))) :
    p.floorCocycle θ v y / p.floorCocycle θ v x ≤
      Real.exp (p.rationalGraphPrefixCost A) := by
  rw [hp.parameter_cocycle_eq_flattened, hp.parameter_cocycle_eq_flattened]
  apply CircleWeights.cocycle_ratio_cap_finite_exceptions
    θ p.flattenedFrequency p.flattenedCost v x y (Finset.range (A - 1))
    (fun k => (hp.flattenedCost_pos k).le)
  · intro k hk
    have hkA : A ≤ k + 1 := by simp only [Finset.mem_range] at hk; omega
    simpa only [CircleWeights.coordinate, CircleWeights.representative,
      flattenedFrequency, coordinate, rep, natCast_zsmul] using hxy (k + 1) hkA
  · simpa only [CircleWeights.coordinate, CircleWeights.representative,
      CircleWeights.phase, flattenedFrequency, coordinate, rep, alpha,
      natCast_zsmul, Int.cast_natCast] using hx
  · simpa only [CircleWeights.coordinate, CircleWeights.representative,
      CircleWeights.phase, flattenedFrequency, coordinate, rep, alpha,
      natCast_zsmul, Int.cast_natCast] using hy

theorem trimmed_floorCocycle_ratio_le {A j n : ℕ} (hA : 1 ≤ A) (hj : 1 ≤ j)
    (x : Circle) (hx : x ∈ p.rationalGraphGood A j) (t : ℝ)
    (ht : p.q A • (t : Circle) = 0)
    (hphase : Int.fract ((n : ℝ) * θ - t) < p.ell j)
    (hn : (n : ℝ) ≤ p.Q j) (hd : p.orbitGraphDensity θ j n x ≠ 0) (v : ℤ)
    (hfx : HasFiniteSupport (fun k : ℕ =>
      Int.floor (p.coordinate (k + 1) x + (v : ℝ) * p.alpha θ (k + 1))))
    (hfy : HasFiniteSupport (fun k : ℕ =>
      Int.floor (p.coordinate (k + 1) (x + (((n : ℝ) * θ : ℝ) : Circle)) +
        (v : ℝ) * p.alpha θ (k + 1)))) :
    p.floorCocycle θ v (x + (((n : ℝ) * θ : ℝ) : Circle)) / p.floorCocycle θ v x ≤
      Real.exp (p.rationalGraphPrefixCost A) :=
  hp.floorCocycle_ratio_le_prefix hA x _ v
    (hp.ordered_of_rationalGraphGood hA hj x hx t ht hphase hn hd) hfx hfy

theorem exists_uniform_rationalGraph_cap_set :
    ∃ s : Set Circle, MeasurableSet s ∧ (∀ᵐ x ∂circleMeasure, x ∈ s) ∧
      (∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s) ∧
      ∀ (A j n : ℕ), 1 ≤ A → 1 ≤ j → ∀ x ∈ s,
        x ∈ p.rationalGraphGood A j → ∀ t : ℝ,
        p.q A • (t : Circle) = 0 →
        Int.fract ((n : ℝ) * θ - t) < p.ell j →
        (n : ℝ) ≤ p.Q j → p.orbitGraphDensity θ j n x ≠ 0 →
        ∀ v : ℤ, p.floorCocycle θ v (x + (((n : ℝ) * θ : ℝ) : Circle)) /
          p.floorCocycle θ v x ≤ Real.exp (p.rationalGraphPrefixCost A) := by
  have hq : ∀ k, p.flattenedFrequency k ≠ 0 := by
    intro k
    change (p.q (k + 1) : ℤ) ≠ 0
    exact_mod_cast (hp.q_pos (k + 1)).ne'
  have hphase : Summable (CircleWeights.phase θ p.flattenedFrequency) := by
    change Summable (fun k : ℕ => Int.fract (((p.q (k + 1) : ℤ) : ℝ) * θ))
    simpa only [alpha, Int.cast_natCast] using hp.summable_phases
  obtain ⟨s, hs, hfull, hinv, hfinite, _⟩ := CircleWeights.exists_cocycle_set
    θ p.flattenedFrequency hq p.flattenedCost hphase
  refine ⟨s, hs, hfull, hinv, ?_⟩
  intro A j n hA hj x hx hgood t ht hph hn hd v
  apply hp.trimmed_floorCocycle_ratio_le hA hj x hgood t ht hph hn hd v
  · simpa only [CircleWeights.coordinate, CircleWeights.representative,
      CircleWeights.phase, flattenedFrequency, coordinate, rep, alpha,
      natCast_zsmul, Int.cast_natCast] using hfinite x hx v
  · have hy := hfinite (CircleWeights.rotate θ (n : ℤ) x) ((hinv (n : ℤ) x).mpr hx) v
    simpa only [CircleWeights.coordinate, CircleWeights.representative,
      CircleWeights.phase, CircleWeights.rotate, flattenedFrequency, coordinate, rep, alpha,
      natCast_zsmul, Int.cast_natCast, ← AddCircle.coe_nsmul, nsmul_eq_mul] using hy

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RationalGraphTrimmingMeasure
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ENNReal
namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem trimming_measurePreserving_coordinate (i : ℕ) :
    MeasurePreserving (p.coordinate i) circleMeasure
      (volume.restrict (Ico (0 : ℝ) 1)) := by
  change MeasurePreserving
    (fun x : UnitAddCircle => ((AddCircle.equivIco (1 : ℝ) 0 (p.q i • x)) : ℝ))
    volume (volume.restrict (Ico (0 : ℝ) 1))
  simpa only [natCast_zsmul] using
    CircleWeightSupport.measurePreserving_characterRepresentative (p.q i : ℤ)
      (by exact_mod_cast (hp.q_pos i).ne')

theorem measure_coordinate_boundary_le (i : ℕ) (b : ℝ) :
    circleMeasure {x | 1 - b ≤ p.coordinate i x} ≤ ENNReal.ofReal b := by
  change circleMeasure (p.coordinate i ⁻¹' Ici (1 - b)) ≤ _
  rw [(hp.trimming_measurePreserving_coordinate i).measure_preimage measurableSet_Ici.nullMeasurableSet,
    Measure.restrict_apply measurableSet_Ici]
  calc
    volume (Ici (1 - b) ∩ Ico 0 1) ≤ volume (Ico (1 - b) 1) := by
      apply measure_mono
      intro z hz
      exact ⟨hz.1, hz.2.2⟩
    _ = ENNReal.ofReal b := by rw [Real.volume_Ico]; congr 1; ring

theorem measure_finite_boundary_union_le (s : Finset ℕ) (b : ℝ) :
    circleMeasure (⋃ i ∈ s, {x | 1 - b ≤ p.coordinate i x}) ≤
      ENNReal.ofReal ((s.card : ℝ) * b) := by
  calc
    _ ≤ ∑ i ∈ s, circleMeasure {x | 1 - b ≤ p.coordinate i x} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ s, ENNReal.ofReal b :=
      Finset.sum_le_sum fun i _ => hp.measure_coordinate_boundary_le i b
    _ = ENNReal.ofReal ((s.card : ℝ) * b) := by
      simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]

theorem measure_future_block_boundary_le (j s : ℕ) (hs : 1 ≤ s) :
    circleMeasure (⋃ i ∈ p.block s,
      {x | 1 - 2 * p.Q j / p.N s ≤ p.coordinate i x}) ≤
      ENNReal.ofReal (2 * p.Q j / (p.K s : ℝ)) := by
  have h := hp.measure_finite_boundary_union_le (p.block s) (2 * p.Q j / p.N s)
  rw [p.card_block s hs] at h
  have hm : (p.m s : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos s hs).ne'
  convert h using 2
  all_goals try with_reducible_and_instances rfl
  unfold N
  field_simp

omit hp in

theorem rationalGraphBad_subset (A j : ℕ) :
    p.rationalGraphBad A j ⊆
      (⋃ i ∈ Finset.Icc A (p.blockEnd (j - 1)),
        {x | 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j ≤ p.coordinate i x}) ∪
      (⋃ n : ℕ, ⋃ i ∈ p.block (j + 1 + n),
        {x | 1 - 2 * p.Q j / p.N (j + 1 + n) ≤ p.coordinate i x}) := by
  intro x hx
  change ¬ ((∀ i, A ≤ i → i ≤ p.blockEnd (j - 1) →
    p.coordinate i x < 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j) ∧
    ∀ s, j < s → ∀ i ∈ p.block s,
      p.coordinate i x < 1 - 2 * p.Q j / p.N s) at hx
  by_cases hearly : ∀ i, A ≤ i → i ≤ p.blockEnd (j - 1) →
      p.coordinate i x < 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j
  · right
    have hfuture : ¬ ∀ s, j < s → ∀ i ∈ p.block s,
        p.coordinate i x < 1 - 2 * p.Q j / p.N s :=
      fun hf => hx ⟨hearly, hf⟩
    push Not at hfuture
    obtain ⟨s, hjs, i, hi, hbad⟩ := hfuture
    have hs : j + 1 + (s - (j + 1)) = s := by omega
    apply mem_iUnion.mpr
    refine ⟨s - (j + 1), ?_⟩
    rw [hs]
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hi, hbad⟩⟩
  · left
    push Not at hearly
    obtain ⟨i, hAi, hia, hi⟩ := hearly
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨Finset.mem_Icc.mpr ⟨hAi, hia⟩, hi⟩⟩

theorem measure_early_boundary_le {A : ℕ} (hA : 1 ≤ A) (j : ℕ) :
    circleMeasure (⋃ i ∈ Finset.Icc A (p.blockEnd (j - 1)),
      {x | 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j ≤ p.coordinate i x}) ≤
      ENNReal.ofReal ((p.blockEnd (j - 1) : ℝ) *
        (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j) := by
  have hcard : (Finset.Icc A (p.blockEnd (j - 1))).card ≤ p.blockEnd (j - 1) := by
    rw [Nat.card_Icc]
    omega
  have hb : 0 ≤ (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j := by
    unfold ell
    positivity
  calc
    _ ≤ ENNReal.ofReal (((Finset.Icc A (p.blockEnd (j - 1))).card : ℝ) *
        ((p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j)) :=
      hp.measure_finite_boundary_union_le _ _
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hb)

theorem measure_future_boundary_le (j : ℕ) :
    circleMeasure (⋃ n : ℕ, ⋃ i ∈ p.block (j + 1 + n),
      {x | 1 - 2 * p.Q j / p.N (j + 1 + n) ≤ p.coordinate i x}) ≤
      ENNReal.ofReal (2 * p.Q j * (∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ))) := by
  have hK : Summable (fun n : ℕ => 1 / (p.K (j + 1 + n) : ℝ)) := by
    have h := (summable_nat_add_iff j).mpr hp.summable_reciprocal
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hsum : Summable (fun n : ℕ => 2 * p.Q j / (p.K (j + 1 + n) : ℝ)) := by
    simpa only [mul_one_div] using hK.mul_left (2 * p.Q j)
  calc
    _ ≤ ∑' n : ℕ, circleMeasure (⋃ i ∈ p.block (j + 1 + n),
        {x | 1 - 2 * p.Q j / p.N (j + 1 + n) ≤ p.coordinate i x}) := measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (2 * p.Q j / (p.K (j + 1 + n) : ℝ)) :=
      ENNReal.tsum_le_tsum fun n => hp.measure_future_block_boundary_le j (j + 1 + n) (by omega)
    _ = ENNReal.ofReal (∑' n : ℕ, 2 * p.Q j / (p.K (j + 1 + n) : ℝ)) := by
      symm
      apply ENNReal.ofReal_tsum_of_nonneg _ hsum
      intro n
      exact div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Nat.cast_nonneg _)
    _ = _ := by
      congr 1
      simpa only [mul_one_div] using
        (tsum_mul_left : (∑' n : ℕ, (2 * p.Q j) *
          (1 / (p.K (j + 1 + n) : ℝ))) =
          (2 * p.Q j) * ∑' n : ℕ, 1 / (p.K (j + 1 + n) : ℝ))

theorem measure_rationalGraphBad_le {A j : ℕ} (hA : 1 ≤ A) (hj : 1 ≤ j) :
    circleMeasure (p.rationalGraphBad A j) ≤
      ENNReal.ofReal (1 / ((j + 1 : ℕ) : ℝ)^2 +
        4 * p.Q j / (p.K (j + 1) : ℝ)) := by
  have hearly := hp.measure_early_boundary_le hA j
  have hfuture := hp.measure_future_boundary_le j
  calc
    _ ≤ circleMeasure ((⋃ i ∈ Finset.Icc A (p.blockEnd (j - 1)),
        {x | 1 - (p.q (p.blockEnd (j - 1)) : ℝ) * p.ell j ≤ p.coordinate i x}) ∪
        (⋃ n : ℕ, ⋃ i ∈ p.block (j + 1 + n),
        {x | 1 - 2 * p.Q j / p.N (j + 1 + n) ≤ p.coordinate i x})) :=
      measure_mono (rationalGraphBad_subset (p := p) A j)
    _ ≤ _ := (measure_union_le _ _).trans ((add_le_add hearly hfuture).trans (by
      rw [← ENNReal.ofReal_add (by unfold ell; positivity) (by
        apply mul_nonneg
        · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        · exact tsum_nonneg fun n => one_div_nonneg.mpr (Nat.cast_nonneg _))]
      exact ENNReal.ofReal_le_ofReal (hp.discarded_mass_bound j hj)))

theorem tendsto_measure_rationalGraphBad {A : ℕ} (hA : 1 ≤ A) :
    Filter.Tendsto (fun n : ℕ => circleMeasure (p.rationalGraphBad A (n + 1)))
      Filter.atTop (nhds 0) := by
  have hbound := ENNReal.tendsto_ofReal hp.tendsto_discarded_mass_bound
  simp only [ENNReal.ofReal_zero] at hbound
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbound
  · intro n
    exact zero_le
  · intro n
    simpa only [Nat.add_assoc] using hp.measure_rationalGraphBad_le hA (show 1 ≤ n + 1 by omega)

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_UniformAbsoluteContinuity
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory
open scoped ENNReal NNReal

namespace Invariant233.UniformlyAbsolutelyContinuous

variable {X ι : Type*} [MeasurableSpace X]

theorem absolutelyContinuous {μ : Measure X} {ν : ι → Measure X}
    (h : UniformlyAbsolutelyContinuous μ ν) (i : ι) : ν i ≪ μ := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  apply le_antisymm ?_ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  obtain ⟨δ, hδ, hbound⟩ := h ε hε
  have hsmall : μ s < (δ : ℝ≥0∞) := by
    rw [hzero]
    exact_mod_cast hδ
  simpa only [bot_eq_zero, zero_add] using (hbound s hs hsmall i).le

end Invariant233.UniformlyAbsolutelyContinuous

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_SimultaneousLusin
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Topology
open scoped ENNReal

namespace Invariant233.SimultaneousLusin

theorem continuousOn_of_finer_compact {X Y : Type*}
    [t : TopologicalSpace X] [hT2 : T2Space X] [TopologicalSpace Y]
    {t' : TopologicalSpace X} (hle : t' ≤ t)
    {K : Set X} (hK : @IsCompact X t' K) {f : X → Y}
    (hf : @Continuous X Y t' _ f) : @ContinuousOn X Y t _ f K := by
  apply (@continuousOn_iff_isClosed X Y t _ f K).2
  intro s hs
  have hC : @IsCompact X t' (K ∩ f ⁻¹' s) :=
    hK.inter_right (hs.preimage hf)
  have hC' : @IsCompact X t (K ∩ f ⁻¹' s) := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t (K ∩ f ⁻¹' s) id hC (continuous_id_of_le hle))
  exact ⟨K ∩ f ⁻¹' s, @IsCompact.isClosed X t hT2 _ hC',
    by ext x; simp [and_comm]⟩

theorem exists_compact_continuousOn {X Y : Type*}
    [t : TopologicalSpace X] [hPolish : PolishSpace X]
    [m : MeasurableSpace X] [hBorel : BorelSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [SecondCountableTopology Y] (μ : Measure X) [IsFiniteMeasure μ]
    {f : X → Y} (hf : Measurable f) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ μ Kᶜ < ε ∧ ContinuousOn f K := by
  obtain ⟨t', hle, hfc, hP'⟩ := hf.exists_continuous
  have hB' : @BorelSpace X t' m := by
    constructor
    exact hBorel.measurable_eq.trans
      (MeasureTheory.borel_eq_borel_of_le hP' hPolish hle).symm
  let : TopologicalSpace X := t'
  let : PolishSpace X := hP'
  let : BorelSpace X := hB'
  obtain ⟨K, -, hK, hsmall⟩ :=
    (MeasurableSet.univ : MeasurableSet (Set.univ : Set X)).exists_isCompact_sdiff_lt
      (measure_ne_top μ Set.univ) hε
  have hKold : @IsCompact X t K := by
    simpa only [image_id] using
      (@IsCompact.image X X t' t K id hK (continuous_id_of_le hle))
  refine ⟨K, hKold, ?_, ?_⟩
  · simpa only [← compl_eq_univ_sdiff] using hsmall
  · exact @continuousOn_of_finer_compact X Y t inferInstance _ t' hle K hK f hfc

end Invariant233.SimultaneousLusin

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongContinuityFromColumns
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Topology

namespace Invariant233.StrongContinuityFromColumns

theorem continuous_apply_of_dense {𝕜 X E F : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) {s : Set E} (hs : Dense s)
    (hcont : ∀ v ∈ s, Continuous (fun x => A x v)) (v : E) :
    Continuous (fun x => A x v) := by
  rw [continuous_iff_continuousAt]
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hden : 0 < 3 * (C + 1) := by positivity
  obtain ⟨w, hw, hvw⟩ := hs.exists_dist_lt v (div_pos hε hden)
  have hvw' : C * dist v w < ε / 3 := by
    have hdist : 0 ≤ dist v w := dist_nonneg
    have hlt : dist v w * (3 * (C + 1)) < ε :=
      (lt_div_iff₀ hden).mp hvw
    nlinarith
  have hevent : ∀ᶠ y in 𝓝 x, dist (A y w) (A x w) < ε / 3 :=
    Metric.tendsto_nhds.mp (hcont w hw).continuousAt (ε / 3) (by positivity)
  filter_upwards [hevent] with y hy
  have hleft : dist (A y v) (A y w) ≤ C * dist v w := by
    calc
      dist (A y v) (A y w) ≤ ‖A y‖ * dist v w := (A y).lipschitz.dist_le_mul v w
      _ ≤ C * dist v w := mul_le_mul_of_nonneg_right (hbound y) dist_nonneg
  have hright : dist (A x w) (A x v) ≤ C * dist v w := by
    calc
      dist (A x w) (A x v) ≤ ‖A x‖ * dist w v := (A x).lipschitz.dist_le_mul w v
      _ ≤ C * dist w v := mul_le_mul_of_nonneg_right (hbound x) dist_nonneg
      _ = C * dist v w := by rw [dist_comm w v]
  have htri := dist_triangle4 (A y v) (A y w) (A x w) (A x v)
  linarith

theorem continuous_apply_of_dense_span {𝕜 X E F ι : Type*}
    [NontriviallyNormedField 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : ι → E)
    (hb : (Submodule.span 𝕜 (Set.range b)).topologicalClosure = ⊤)
    (hcont : ∀ i, Continuous (fun x => A x (b i))) (v : E) :
    Continuous (fun x => A x v) := by
  apply continuous_apply_of_dense A hC hbound
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr hb) _ v
  intro w hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨i, rfl⟩ := hw
      exact hcont i
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : X => (0 : F)))
  | add w z hw hz hwc hzc =>
      simpa only [map_add, Pi.add_def] using hwc.add hzc
  | smul c w hw hwc =>
      simpa only [map_smul, Pi.smul_def] using hwc.const_smul c

theorem continuous_apply_of_hilbertBasis {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcont : ∀ i, Continuous (fun x => A x (b i))) (v : E) :
    Continuous (fun x => A x v) :=
  continuous_apply_of_dense_span A hC hbound b b.dense_span hcont v

theorem continuousOn_apply_of_hilbertBasis {𝕜 X E F ι : Type*}
    [RCLike 𝕜] [TopologicalSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C) {Q : Set X}
    (hbound : ∀ x ∈ Q, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcont : ∀ i, ContinuousOn (fun x => A x (b i)) Q) (v : E) :
    ContinuousOn (fun x => A x v) Q := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_apply_of_hilbertBasis (fun x : Q => A x) hC
    (fun x => hbound x x.property) b (fun i => (hcont i).domRestrict) v

end Invariant233.StrongContinuityFromColumns

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_StrongLusin
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open scoped ENNReal

namespace Invariant233.StrongLusin

theorem exists_compact_strong_and_continuousOn {𝕜 X E F ι J : Type*}
    {Y : J → Type*}
    [RCLike 𝕜] [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
    [∀ j, TopologicalSpace (Y j)] [∀ j, MeasurableSpace (Y j)]
    [∀ j, OpensMeasurableSpace (Y j)] [∀ j, SecondCountableTopology (Y j)]
    [Countable ι] [Countable J] (μ : Measure X) [IsFiniteMeasure μ]
    (A : X → E →L[𝕜] F) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x, ‖A x‖ ≤ C) (b : HilbertBasis ι 𝕜 E)
    (hcolumns : ∀ i, Measurable (fun x => A x (b i)))
    (g : ∀ j, X → Y j) (hg : ∀ j, Measurable (g j))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ Q : Set X, IsCompact Q ∧ μ Qᶜ < ε ∧
      (∀ v : E, ContinuousOn (fun x => A x v) Q) ∧
      ∀ j, ContinuousOn (g j) Q := by
  have hmeas : Measurable (fun x => ((fun i => A x (b i)), (fun j => g j x))) :=
    (Measurable.of_eval hcolumns).prodMk (Measurable.of_eval hg)
  obtain ⟨Q, hQ, hsmall, hcont⟩ :=
    SimultaneousLusin.exists_compact_continuousOn μ hmeas hε
  refine ⟨Q, hQ, hsmall, ?_, continuousOn_pi.mp hcont.snd⟩
  exact fun v => StrongContinuityFromColumns.continuousOn_apply_of_hilbertBasis A hC
    (fun x _ => hbound x) b (continuousOn_pi.mp hcont.fst) v

end Invariant233.StrongLusin

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Operators_OperatorCompactTransfer
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal lp

noncomputable section
namespace Invariant233.CompactTransfer

local instance operatorCompactTransferSecondCountableTopology :
    SecondCountableTopology (SequenceHilbert ℤ) := by
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hs := (Set.countable_range b).isSeparable.span (R := ℂ) |>.closure
  have : TopologicalSpace.SeparableSpace (SequenceHilbert ℤ) :=
    TopologicalSpace.isSeparable_univ_iff.mp (by
      simpa only [← Submodule.topologicalClosure_coe, b.dense_span, Submodule.top_coe] using hs)
  first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem uniform_marginal_budget {X ι : Type*}
    [MeasurableSpace X] (μ : Measure X) (νs : ι → Measure (X × X))
    (hfirst : UniformlyAbsolutelyContinuous μ (fun i => (νs i).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ (fun i => (νs i).map Prod.snd)) :
    ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        νs i (A ×ˢ Set.univ) + νs i (Set.univ ×ˢ A) ≤ ε := by
  intro ε hε
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨δ₁, hδ₁, hfirst⟩ := hfirst (ε / 2) hhalf
  obtain ⟨δ₂, hδ₂, hsecond⟩ := hsecond (ε / 2) hhalf
  refine ⟨(min δ₁ δ₂ : ℝ≥0), ?_, ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (ne_of_gt (lt_min hδ₁ hδ₂))
  intro A hA hμ i
  have hμ₁ : μ A < (δ₁ : ℝ≥0∞) := hμ.trans_le (by exact_mod_cast min_le_left δ₁ δ₂)
  have hμ₂ : μ A < (δ₂ : ℝ≥0∞) := hμ.trans_le (by exact_mod_cast min_le_right δ₁ δ₂)
  have h₁ := hfirst A hA hμ₁ i
  have h₂ := hsecond A hA hμ₂ i
  rw [Measure.map_apply measurable_fst hA] at h₁
  rw [Measure.map_apply measurable_snd hA] at h₂
  have heq₁ : Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set X) := by ext t; simp
  have heq₂ : Prod.snd ⁻¹' A = (Set.univ : Set X) ×ˢ A := by ext t; simp
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  calc
    νs i (A ×ˢ Set.univ) + νs i (Set.univ ×ˢ A) ≤
        ((ε / 2 : ℝ≥0) : ℝ≥0∞) + ((ε / 2 : ℝ≥0) : ℝ≥0∞) :=
      add_le_add h₁.le h₂.le
    _ = ε := by rw [← ENNReal.coe_add, add_halves]

theorem capped_operator_relation_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    (C : ℝ) (hC : 0 ≤ C) (hpn : ∀ x, ‖p x‖ ≤ C)
    (B : ℝ) (hB : 0 ≤ B)
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ δ : ℝ≥0∞, δ ≠ 0 ∧
      ∀ A : Set X, MeasurableSet A → μ A < δ → ∀ i,
        (νs i : Measure (X × X)) (A ×ˢ Set.univ) +
        (νs i : Measure (X × X)) (Set.univ ×ˢ A) ≤ ε)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0 := by
  classical
  let b : HilbertBasis ℤ ℂ (SequenceHilbert ℤ) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hb : ∀ i, b i = lp.single 2 i (1 : ℂ) := fun i => (b.repr_symm_single i).symm
  apply ae_mem_of_closed_approximation hν
  intro ε hε
  obtain ⟨δ, hδ, hδsmall⟩ := hsmall ε hε
  obtain ⟨Q, hQ, hμQ, hpQ, hFQ⟩ :=
    StrongLusin.exists_compact_strong_and_continuousOn μ p hC hpn b
      (fun i => by simpa only [hb] using hpm i) F hFm hδ
  let S : Set (X × X) := {t | t ∈ Q ×ˢ Q ∧
    (1 - p t.2).comp ((cappedDiagonal F hF B hB t).comp (p t.1)) = 0}
  have hScompact : IsCompact S := by
    apply isCompact_diagonal_relation_on Q hQ p
      (fun t i => ((min B (F i t.2 / F i t.1) : ℝ) : ℂ)) B C hB
      (fun t i => ?_) hpQ (fun i => ?_) hpn
    · have hn : 0 ≤ min B (F i t.2 / F i t.1) :=
        le_min hB (div_nonneg (hF i t.2).le (hF i t.1).le)
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn] using
        (min_le_left B (F i t.2 / F i t.1))
    · exact continuousOn_capped_ratio (F i) Q (hFQ i)
        (fun x _ => (hF i x).ne') B
  refine ⟨S, hScompact.isClosed, fun _ ht => ht.2,
    Filter.Eventually.of_forall ?_⟩
  intro i
  have hsub : ∀ᵐ t ∂(νs i : Measure (X × X)), t ∈ Sᶜ → t ∈ (Q ×ˢ Q)ᶜ := by
    filter_upwards [hzero i] with t ht
    intro hbad hQpair
    exact hbad ⟨hQpair, ht⟩
  apply (measure_mono_ae hsub).trans
  rw [Set.compl_prod_eq_union]
  exact (measure_union_le _ _).trans
    (hδsmall Qᶜ hQ.isClosed.measurableSet.compl hμQ i)

theorem cappedDiagonal_eq_ratioDiagonal {X : Type*} (F : ℤ → X → ℝ)
    (hF : ∀ i x, 0 < F i x) (B : ℝ) (hB : 0 ≤ B) (t : X × X)
    (hcap : ∀ i, F i t.2 / F i t.1 ≤ B) :
    cappedDiagonal F hF B hB t = ratioDiagonal F t := by
  have hnorm : ∀ i, ‖((F i t.2 / F i t.1 : ℝ) : ℂ)‖ ≤ B := by
    intro i
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hF i t.2).le (hF i t.1).le)] using hcap i
  unfold ratioDiagonal
  rw [SequenceHilbert.boundedDiagonal_eq _ B hB hnorm]
  apply SequenceHilbert.diagonal_congr
  intro i
  simp only [min_eq_right (hcap i)]

theorem compact_operator_transfer {X ι : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hp : ∀ x, IsStarProjection (p x))
    (F : ℤ → X → ℝ) (hF : ∀ i x, 0 < F i x)
    (hFm : ∀ i, Measurable (F i))
    (hpm : ∀ i : ℤ, Measurable (fun x => p x (lp.single 2 i 1)))
    {L : Filter ι} [L.NeBot] {ν : FiniteMeasure (X × X)}
    {νs : ι → FiniteMeasure (X × X)} (hν : Tendsto νs L (𝓝 ν))
    (hfirst : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous μ
      (fun i => (νs i : Measure (X × X)).map Prod.snd))
    (B : ℝ) (hB : 0 < B)
    (hcapn : ∀ i k, ∀ᵐ t ∂(νs i : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hcap : ∀ k, ∀ᵐ t ∂(ν : Measure (X × X)), F k t.2 / F k t.1 ≤ B)
    (hzero : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0) :
    ∀ᵐ t ∂(ν : Measure (X × X)),
      (1 - p t.2).comp ((ratioDiagonal F t).comp (p t.1)) = 0 := by
  have hsmall := uniform_marginal_budget μ
    (fun i => (νs i : Measure (X × X))) hfirst hsecond
  have hbounded : ∀ x, ‖p x‖ ≤ (1 : ℝ) :=
    fun x => IsStarProjection.norm_le (p x) (hp x)
  have hzerocap : ∀ i, ∀ᵐ t ∂(νs i : Measure (X × X)),
      (1 - p t.2).comp ((cappedDiagonal F hF B hB.le t).comp (p t.1)) = 0 := by
    intro i
    filter_upwards [ae_all_iff.mpr (hcapn i), hzero i] with t ht hz
    rwa [cappedDiagonal_eq_ratioDiagonal F hF B hB.le t ht]
  have hresult := capped_operator_relation_transfer μ p F hF hFm hpm
    1 zero_le_one hbounded B hB.le hν hsmall hzerocap
  filter_upwards [ae_all_iff.mpr hcap, hresult] with t ht hz
  rwa [cappedDiagonal_eq_ratioDiagonal F hF B hB.le t ht] at hz

end Invariant233.CompactTransfer

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRationalGraphCaps
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Function
open scoped BigOperators

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem ae_flattened_floor_support :
    ∀ᵐ x ∂circleMeasure, ∀ k : ℤ,
      HasFiniteSupport (fun i : ℕ => Int.floor
        (CircleWeights.coordinate p.flattenedFrequency i x +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency i)) := by
  have hq : ∀ i, p.flattenedFrequency i ≠ 0 := by
    intro i
    change (p.q (i + 1) : ℤ) ≠ 0
    exact_mod_cast (hp.q_pos (i + 1)).ne'
  have hs : Summable (CircleWeights.phase θ p.flattenedFrequency) := by
    change Summable (fun i : ℕ => Int.fract ((p.q (i + 1) : ℝ) * θ))
    exact hp.summable_phases
  exact CircleWeightSupport.ae_all_int_finite_floor_support
    p.flattenedFrequency hq (CircleWeights.phase θ p.flattenedFrequency)
    (CircleWeights.phase_nonneg θ p.flattenedFrequency) hs

theorem ae_all_rational_graph_floor_support :
    ∀ᵐ x ∂circleMeasure,
      (∀ k : ℤ, HasFiniteSupport (fun i : ℕ => Int.floor
        (CircleWeights.coordinate p.flattenedFrequency i x +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency i))) ∧
      ∀ (A : ℕ) (r : ℤ) (k : ℤ), HasFiniteSupport (fun i : ℕ => Int.floor
        (CircleWeights.coordinate p.flattenedFrequency i
          (x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle)) +
          (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency i)) := by
  refine hp.ae_flattened_floor_support.and ?_
  apply ae_all_iff.mpr
  intro A
  apply ae_all_iff.mpr
  intro r
  have hmp : MeasurePreserving
      (fun x : Circle => x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle))
      circleMeasure circleMeasure := by
    change MeasurePreserving _ volume volume
    exact measurePreserving_add_right volume _
  let P : Circle → Prop := fun y => ∀ k : ℤ, HasFiniteSupport (fun i : ℕ =>
    Int.floor (CircleWeights.coordinate p.flattenedFrequency i y +
      (k : ℝ) * CircleWeights.phase θ p.flattenedFrequency i))
  have hP : ∀ᵐ y ∂circleMeasure, P y := hp.ae_flattened_floor_support
  exact hmp.quasiMeasurePreserving.ae (p := P) hP

theorem ae_rational_graph_ratio_cap :
    ∀ᵐ x ∂circleMeasure, ∀ (A : ℕ), 1 ≤ A → ∀ (r k : ℤ),
      p.floorCocycle θ k
          (x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle)) /
        p.floorCocycle θ k x ≤
          Real.exp (∑ i ∈ Finset.range (A - 1), p.flattenedCost i) := by
  filter_upwards [hp.ae_all_rational_graph_floor_support] with x hx
  intro A hA r k
  rw [hp.parameter_cocycle_eq_flattened, hp.parameter_cocycle_eq_flattened]
  apply CircleWeights.cocycle_ratio_cap_finite_exceptions θ
    p.flattenedFrequency p.flattenedCost k _ _ (Finset.range (A - 1))
    (fun i => (hp.flattenedCost_pos i).le) _ (hx.1 k) (hx.2 A r k)
  intro i hi
  have hAi : A ≤ i + 1 := by
    simp only [Finset.mem_range, not_lt] at hi
    omega
  have he := hp.trimming_coordinate_rational_translation hAi r x
  change p.coordinate (i + 1) x ≤ p.coordinate (i + 1)
    (x + (((r : ℝ) / (p.q A : ℝ) : ℝ) : Circle))
  exact le_of_eq he.symm

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRationalGraphTransfer
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Invariant233.CircleParameterLaws

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem rational_graph_measure_ratio_cap (A : ℕ) (hA : 1 ≤ A) (r k : ℤ) :
    ∀ᵐ z ∂(circleTranslationGraph (p.rationalTranslation A r) : Measure (Circle × Circle)),
      p.floorCocycle θ k z.2 / p.floorCocycle θ k z.1 ≤ p.rationalRatioBound A := by
  change ∀ᵐ z ∂circleMeasure.map (fun x => (x, x + p.rationalTranslation A r)), _
  apply (ae_map_iff (measurable_id.prodMk
    (measurable_id.add measurable_const)).aemeasurable ?_).mpr
  · filter_upwards [hp.ae_rational_graph_ratio_cap] with x hx
    exact hx A hA r k
  · exact measurableSet_le
      ((hp.measurable_parameter_cocycle k).comp measurable_snd |>.div
        ((hp.measurable_parameter_cocycle k).comp measurable_fst)) measurable_const

theorem rational_graph_identity_of_approximants
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hP : ∀ x, IsStarProjection (P x))
    (hPm : ∀ k : ℤ, Measurable (fun x => P x (lp.single 2 k 1)))
    (A : ℕ) (hA : 1 ≤ A) (r : ℤ)
    (ν : ℕ → FiniteMeasure (Circle × Circle))
    (hν : Tendsto ν atTop (𝓝 (circleTranslationGraph (p.rationalTranslation A r))))
    (hfirst : UniformlyAbsolutelyContinuous circleMeasure
      (fun j => (ν j : Measure (Circle × Circle)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous circleMeasure
      (fun j => (ν j : Measure (Circle × Circle)).map Prod.snd))
    (hcap : ∀ j k, ∀ᵐ z ∂(ν j : Measure (Circle × Circle)),
      p.floorCocycle θ k z.2 / p.floorCocycle θ k z.1 ≤ p.rationalRatioBound A)
    (hzero : ∀ j, ∀ᵐ z ∂(ν j : Measure (Circle × Circle)),
      (1 - P z.2).comp ((ratioDiagonal (p.floorCocycle θ) z).comp (P z.1)) = 0) :
    ∀ᵐ x ∂circleMeasure,
      (1 - P (x + p.rationalTranslation A r)) *
        ratioDiagonal (p.floorCocycle θ) (x, x + p.rationalTranslation A r) * P x = 0 := by
  let : IsFiniteMeasure circleMeasure := by
    change IsFiniteMeasure (volume : Measure Circle)
    first | (set_option synthInstance.maxHeartbeats 20000 in infer_instance) | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)
  have hlim := CompactTransfer.compact_operator_transfer circleMeasure P hP
    (p.floorCocycle θ) (fun k x => p.floorCocycle_pos θ k x)
    hp.measurable_parameter_cocycle hPm hν hfirst hsecond
    (p.rationalRatioBound A) (Real.exp_pos _)
    hcap (fun k => hp.rational_graph_measure_ratio_cap A hA r k) hzero
  have h := ae_of_ae_map
    (measurable_id.prodMk (measurable_id.add measurable_const)).aemeasurable hlim
  filter_upwards [h] with x hx
  exact hx

theorem rational_graph_identity_of_orbit_approximants
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hP : ∀ x, IsStarProjection (P x))
    (hPm : ∀ k : ℤ, Measurable (fun x => P x (lp.single 2 k 1)))
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂circleMeasure,
      (1 - P (CircleWeights.rotate θ (n : ℤ) x)).comp
        ((ratioDiagonal (p.floorCocycle θ)
          (x, CircleWeights.rotate θ (n : ℤ) x)).comp (P x)) = 0)
    (A : ℕ) (hA : 1 ≤ A) (r : ℤ)
    (ν : ℕ → FiniteMeasure (Circle × Circle))
    (hν : Tendsto ν atTop (𝓝 (circleTranslationGraph (p.rationalTranslation A r))))
    (hfirst : UniformlyAbsolutelyContinuous circleMeasure
      (fun j => (ν j : Measure (Circle × Circle)).map Prod.fst))
    (hsecond : UniformlyAbsolutelyContinuous circleMeasure
      (fun j => (ν j : Measure (Circle × Circle)).map Prod.snd))
    (hcap : ∀ j k, ∀ᵐ z ∂(ν j : Measure (Circle × Circle)),
      p.floorCocycle θ k z.2 / p.floorCocycle θ k z.1 ≤ p.rationalRatioBound A)
    (hsupport : ∀ j, ∀ᵐ z ∂(ν j : Measure (Circle × Circle)),
      ∃ n : ℕ, 0 < n ∧ z.2 = CircleWeights.rotate θ (n : ℤ) z.1) :
    ∀ᵐ x ∂circleMeasure,
      (1 - P (x + p.rationalTranslation A r)) *
        ratioDiagonal (p.floorCocycle θ) (x, x + p.rationalTranslation A r) * P x = 0 := by
  apply hp.rational_graph_identity_of_approximants P hP hPm A hA r ν hν hfirst hsecond hcap
  intro j
  apply Fields.ae_pair_relation_of_countable_graphs
    (fun x y => (1 - P y).comp ((ratioDiagonal (p.floorCocycle θ) (x, y)).comp (P x)) = 0)
    (fun n : ℕ+ => CircleWeights.rotate θ (n : ℤ))
    (hfirst.absolutelyContinuous j)
  · intro n
    exact horbit n n.property
  · filter_upwards [hsupport j] with z hz
    obtain ⟨n, hn, he⟩ := hz
    exact ⟨⟨n, hn⟩, he⟩

omit hp in
theorem rationalGraphIdentities_of_forall (_hp : CircleParameterLaws θ p)
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (h : ∀ A : ℕ, 1 ≤ A → ∀ r : ℤ, ∀ᵐ x ∂circleMeasure,
      (1 - P (x + p.rationalTranslation A r)) *
        ratioDiagonal (p.floorCocycle θ) (x, x + p.rationalTranslation A r) * P x = 0) :
    p.RationalGraphIdentities θ P := by
  apply ae_all_iff.mpr
  intro A
  by_cases hA : 1 ≤ A
  · filter_upwards [ae_all_iff.mpr (h A hA)] with x hx
    exact fun _ => hx
  · exact Filter.Eventually.of_forall fun _ hAx => (hA hAx).elim

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_WeightedGraphMarginals
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace Invariant233.WeightedGraphMarginals

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem map_snd_graph (μ : Measure X) {T : X → Y} (hT : Measurable T) :
    (μ.map (fun x => (x, T x))).map Prod.snd = μ.map T := by
  have hg : Measurable (fun x => (x, T x)) := measurable_id.prodMk hT
  rw [Measure.map_map measurable_snd hg]
  rfl

theorem map_withDensity_inverse (μ : Measure X) {T S : X → X}
    (hT : MeasurePreserving T μ μ) (hS : Measurable S)
    (hST : ∀ x, S (T x) = x) {f : X → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map T = μ.withDensity (fun y => f (S y)) := by
  ext s hs
  rw [Measure.map_apply hT.measurable hs,
    withDensity_apply _ (hT.measurable hs), withDensity_apply _ hs]
  rw [← lintegral_indicator (hT.measurable hs), ← lintegral_indicator hs]
  have h := hT.lintegral_comp ((hf.comp hS).indicator hs)
  convert h using 1 <;> first | (with_reducible_and_instances rfl) | (apply lintegral_congr <;> intro x <;> simp only [Set.indicator, Function.comp_apply, Set.mem_preimage, hST])
  all_goals rfl

end Invariant233.WeightedGraphMarginals

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleSamplingGraph
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.CircleParameterData.blockEnd_zero _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ENNReal

namespace Invariant233.CircleParameterData

theorem samplingTranslation_measurePreserving (θ : ℝ) (n : ℕ) :
    MeasurePreserving (samplingTranslation θ n) circleMeasure circleMeasure := by
  change MeasurePreserving (fun x : Circle => x + (((n : ℝ) * θ : ℝ) : Circle))
    volume volume
  exact measurePreserving_add_right volume (((n : ℝ) * θ : ℝ) : Circle)

theorem coordinate_sub_samplingTranslation (p : CircleParameterData) (θ : ℝ)
    (i n : ℕ) (x : Circle) :
    p.coordinate i (x - (((n : ℝ) * θ : ℝ) : Circle)) =
      Int.fract (p.coordinate i x - (n : ℝ) * p.alpha θ i) := by
  have h := CircleCharacterDynamics.character_orbit_representative
    (p.q i : ℤ) (-(n : ℤ)) θ x
  simpa only [coordinate, rep, alpha, neg_zsmul, natCast_zsmul,
    ← AddCircle.coe_nsmul, nsmul_eq_mul, Int.cast_neg, Int.cast_natCast,
    neg_mul, sub_eq_add_neg] using h

theorem kernel_fract_first (m : ℕ) (z v : ℝ) :
    kernel m (Int.fract z) v = kernel m z v := by
  unfold kernel delta
  rw [Int.fract_fract]

theorem fract_sub_fract_right (z v : ℝ) :
    Int.fract (z - Int.fract v) = Int.fract (z - v) := by
  have he : z - Int.fract v = z - v + (⌊v⌋ : ℤ) := by
    rw [Int.fract]
    ring
  rw [he, Int.fract_add_intCast]

theorem samplingDensity_inverse_translation (p : CircleParameterData) (θ : ℝ)
    (j n : ℕ) (x : Circle) :
    p.samplingDensity θ j n false (x - (((n : ℝ) * θ : ℝ) : Circle)) =
      p.samplingDensity θ j n true x := by
  unfold samplingDensity
  apply Finset.prod_congr rfl
  intro i hi
  rw [p.coordinate_sub_samplingTranslation]
  simp only [orientedKernel, Bool.false_eq_true, ↓reduceIte, kernel_fract_first]
  unfold kernel delta
  rw [fract_sub_fract_right]

theorem samplingGraph_second_marginal (p : CircleParameterData) (θ : ℝ)
    (j n : ℕ) :
    (p.samplingGraph θ j n).map Prod.snd =
      circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingDensity θ j n true x)) := by
  rw [samplingGraph, WeightedGraphMarginals.map_snd_graph _
    (samplingTranslation_measurable θ n)]
  rw [WeightedGraphMarginals.map_withDensity_inverse circleMeasure
    (samplingTranslation_measurePreserving θ n)
    (S := fun x => x - (((n : ℝ) * θ : ℝ) : Circle))
    (continuous_id.sub continuous_const).measurable
    (fun x => by simp [samplingTranslation])
    (p.measurable_samplingDensity θ j n false).ennreal_ofReal]
  congr 1
  funext x
  rw [p.samplingDensity_inverse_translation]

theorem samplingGraphAverage_second_marginal (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 0 < p.m j) :
    (p.samplingGraphAverage θ j r).map Prod.snd =
      circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingAverage θ j r true x)) := by
  rw [samplingGraphAverage, Measure.map_smul,
    WeightedGraphMarginals.map_finset_sum _ _ measurable_snd]
  simp_rw [p.samplingGraph_second_marginal]
  exact (WeightedGraphMarginals.withDensity_real_finset_sum circleMeasure
    (p.samples j r) (fun n => p.samplingDensity θ j n true)
    (fun n _ => p.measurable_samplingDensity θ j n true)
    (fun n _ x => p.samplingDensity_nonneg θ j n true hm x)
    (by positivity : 0 ≤ 1 / ((p.samples j r).card : ℝ))).symm

theorem samplingGraph_ae_graph (p : CircleParameterData) (θ : ℝ) (j n : ℕ) :
    ∀ᵐ xy ∂p.samplingGraph θ j n, xy.2 = samplingTranslation θ n xy.1 := by
  unfold samplingGraph
  have hg : Measurable (fun x => (x, samplingTranslation θ n x)) :=
    measurable_id.prodMk (samplingTranslation_measurable θ n)
  apply (ae_map_iff hg.aemeasurable ?_).2
  · exact Filter.Eventually.of_forall fun _ => rfl
  · exact (isClosed_eq continuous_snd
      (continuous_fst.add continuous_const)).measurableSet

theorem samplingGraph_ae_positive_density (p : CircleParameterData) (θ : ℝ)
    (j n : ℕ) :
    ∀ᵐ xy ∂p.samplingGraph θ j n, 0 < p.samplingDensity θ j n false xy.1 := by
  unfold samplingGraph
  have hg : Measurable (fun x => (x, samplingTranslation θ n x)) :=
    measurable_id.prodMk (samplingTranslation_measurable θ n)
  apply (ae_map_iff hg.aemeasurable
    (measurableSet_lt measurable_const
      ((p.measurable_samplingDensity θ j n false).comp measurable_fst))).2
  apply (ae_withDensity_iff (p.measurable_samplingDensity θ j n false).ennreal_ofReal).2
  exact Filter.Eventually.of_forall fun x hx =>
    ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr hx)

theorem samplingGraphAverage_ae_graph (p : CircleParameterData) (θ : ℝ) (j r : ℕ) :
    ∀ᵐ xy ∂p.samplingGraphAverage θ j r,
      ∃ n ∈ p.samples j r, xy.2 = samplingTranslation θ n xy.1 := by
  unfold samplingGraphAverage
  apply ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro n hn
  filter_upwards [p.samplingGraph_ae_graph θ j n] with xy hxy
  exact ⟨n, hn, hxy⟩

theorem samplingGraphAverage_ae_positive_density_graph (p : CircleParameterData)
    (θ : ℝ) (j r : ℕ) :
    ∀ᵐ xy ∂p.samplingGraphAverage θ j r,
      ∃ n ∈ p.samples j r, 0 < p.samplingDensity θ j n false xy.1 ∧
        xy.2 = samplingTranslation θ n xy.1 := by
  unfold samplingGraphAverage
  apply ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro n hn
  filter_upwards [p.samplingGraph_ae_graph θ j n,
    p.samplingGraph_ae_positive_density θ j n] with xy hxy hpos
  exact ⟨n, hn, hpos, hxy⟩

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws

open CircleParameterData

theorem samplingAverage_eLpNorm_le_two {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) (hj : 1 ≤ j) (r : ℕ)
    (hr : r < p.q (p.blockEnd (j - 1))) (endpoint : Bool) :
    eLpNorm (p.samplingAverage θ j r endpoint) 2 circleMeasure ≤ 2 := by
  let : IsProbabilityMeasure circleMeasure := by
    constructor
    change volume (Set.univ : Set Circle) = 1
    exact UnitAddCircle.measure_univ
  have he := eLpNorm_add_le (hf := ((p.measurable_samplingAverage θ j r endpoint).sub measurable_const).aestronglyMeasurable) (hg := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability)
    (f := fun x => p.samplingAverage θ j r endpoint x - 1)
    (g := fun _ : Circle => (1 : ℝ)) (μ := circleMeasure)
    (by norm_num : (1 : ENNReal) ≤ 2)
  have hfun : (fun x => p.samplingAverage θ j r endpoint x - 1) +
      (fun _ : Circle => (1 : ℝ)) = p.samplingAverage θ j r endpoint := by
    funext x
    simp
  rw [hfun] at he
  have hc : eLpNorm (fun _ : Circle => (1 : ℝ)) 2 circleMeasure = 1 := by
    rw [eLpNorm_const' _ (by norm_num) (by norm_num)]
    simp
  rw [hc] at he
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hfrac : ENNReal.ofReal (1 / (j : ℝ)) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hjR
  calc
    _ ≤ eLpNorm (fun x => p.samplingAverage θ j r endpoint x - 1) 2 circleMeasure + 1 := he
    _ ≤ ENNReal.ofReal (1 / (j : ℝ)) + 1 :=
      add_le_add (hp.sampling_L2 j hj r hr endpoint).le le_rfl
    _ ≤ (1 : ENNReal) + 1 := add_le_add hfrac le_rfl
    _ = 2 := by norm_num

theorem samplingGraphAverage_ae_positive_graph {θ : ℝ} {p : CircleParameterData}
    (hp : CircleParameterLaws θ p) (j : ℕ) (hj : 1 ≤ j) (r : ℕ)
    (hr : r < p.q (p.blockEnd (j - 1))) :
    ∀ᵐ xy ∂p.samplingGraphAverage θ j r,
      ∃ n ∈ p.samples j r, 0 < n ∧ xy.2 = samplingTranslation θ n xy.1 := by
  filter_upwards [p.samplingGraphAverage_ae_graph θ j r] with xy hxy
  obtain ⟨n, hn, he⟩ := hxy
  exact ⟨n, hn, hp.samples_positive j hj r hr n hn, he⟩

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_CircleSamplingGraphLimits
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.CircleCoupling.hybridPoint_const _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T _root_.OAI.Invariant233.ProductModel.coe_weightedElement _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_add _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_mul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_one _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_smul _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_star _root_.OAI.Invariant233.ProductModel.continuousValueMultiplier_zero _root_.OAI.Invariant233.ProductModel.prefixEndpoint_apply _root_.OAI.Invariant233.ProductModel.productTracialState_apply _root_.OAI.Invariant233.ProductModel.weightedOperator_eq_shift_mul_weightMultiplier _root_.OAI.Invariant233.Rotation.action_add _root_.OAI.Invariant233.Rotation.action_zero _root_.OAI.Invariant233.Rotation.character_norm _root_.OAI.Invariant233.Rotation.orbitWeight_apply _root_.OAI.Invariant233.Rotation.representation_add _root_.OAI.Invariant233.Rotation.representation_mul _root_.OAI.Invariant233.Rotation.representation_one _root_.OAI.Invariant233.Rotation.representation_smul _root_.OAI.Invariant233.Rotation.representation_star _root_.OAI.Invariant233.Rotation.representation_zero _root_.OAI.Invariant233.SamplingTests.spatialLaw_eq_volume _root_.OAI.Invariant233.circleMeasure_singleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Invariant233.CircleParameterLaws

open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem samplingAverage_error_tendsto_zero
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1)))
    (hjt : Tendsto j atTop atTop) (endpoint : Bool) :
    Tendsto (fun n => eLpNorm (fun x => p.samplingAverage θ (j n) (r n) endpoint x - 1)
      2 circleMeasure) atTop (𝓝 0) := by
  have hlim := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_one_div_atTop_nhds_zero_nat.comp hjt)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (show Tendsto (fun n => ENNReal.ofReal (1 / (j n : ℝ))) atTop (𝓝 0) from by
      simpa only [Function.comp_def, ENNReal.ofReal_zero] using hlim)
    (fun _ => bot_le)
    (fun n => (hp.sampling_L2 (j n) (hj n) (r n) (hr n) endpoint).le)

theorem tendsto_samplingGraph_first_marginal
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1)))
    (hjt : Tendsto j atTop atTop) :
    Tendsto (fun n => (p.samplingGraphFinite θ (j n) (r n) (hp.m_pos _ (hj n))).map Prod.fst)
      atTop (𝓝 circleFiniteBase) := by
  apply GraphMeasureConvergence.tendsto_of_density_L2 circleFiniteBase _
    (fun n => p.samplingAverage θ (j n) (r n) false)
  · intro n
    exact p.memLp_samplingAverage θ (j n) (r n) false (hp.m_pos _ (hj n)) 2
  · intro n
    exact Eventually.of_forall fun x =>
      (p.samplingAverage_bounds θ (j n) (r n) false (hp.m_pos _ (hj n)) x).1
  · intro n
    exact p.samplingGraphAverage_first_marginal θ (j n) (r n) (hp.m_pos _ (hj n))
  · exact hp.samplingAverage_error_tendsto_zero j r hj hr hjt false

theorem samplingGraph_marginals_uniformlyAbsolutelyContinuous
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1))) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun n => (p.samplingGraphAverage θ (j n) (r n)).map Prod.fst) ∧
    UniformlyAbsolutelyContinuous circleMeasure
      (fun n => (p.samplingGraphAverage θ (j n) (r n)).map Prod.snd) := by
  let : IsFiniteMeasure circleMeasure := by unfold circleMeasure; infer_instance
  have hden (endpoint : Bool) : UniformlyAbsolutelyContinuous circleMeasure
      (fun n => circleMeasure.withDensity
        (fun x => ENNReal.ofReal (p.samplingAverage θ (j n) (r n) endpoint x))) := by
    apply EndpointLoss.uniformlyAbsolutelyContinuous_withDensity circleMeasure
      (fun n => p.samplingAverage θ (j n) (r n) endpoint)
      (fun n => p.memLp_samplingAverage θ (j n) (r n) endpoint (hp.m_pos _ (hj n)) 2)
      (fun n => Eventually.of_forall fun x =>
        (p.samplingAverage_bounds θ (j n) (r n) endpoint (hp.m_pos _ (hj n)) x).1) 2
    intro n
    rw [EndpointLoss.sqrt_integral_sq_eq_toReal_eLpNorm
      (p.memLp_samplingAverage θ (j n) (r n) endpoint (hp.m_pos _ (hj n)) 2)]
    have h := ENNReal.toReal_mono (by norm_num : (2 : ENNReal) ≠ ∞)
      (hp.samplingAverage_eLpNorm_le_two (j n) (hj n) (r n) (hr n) endpoint)
    simpa only [ENNReal.toReal_ofNat] using h
  constructor
  · convert hden false using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact p.samplingGraphAverage_first_marginal θ (j n) (r n) (hp.m_pos _ (hj n))
  · convert hden true using 1
    all_goals try with_reducible_and_instances rfl
    funext n
    exact p.samplingGraphAverage_second_marginal θ (j n) (r n) (hp.m_pos _ (hj n))

theorem ell_nonneg_and_le (j : ℕ) : 0 ≤ p.ell j ∧
    p.ell j ≤ 1 / ((j + 1 : ℕ) : ℝ)^2 := by
  have hq : (1 : ℝ) ≤ p.q (p.blockEnd (j - 1)) := by
    exact_mod_cast hp.q_pos (p.blockEnd (j - 1))
  have ha : 0 ≤ (p.blockEnd (j - 1) : ℝ) := Nat.cast_nonneg _
  have hj : (0 : ℝ) < ((j + 1 : ℕ) : ℝ)^2 := by positivity
  have hprod : 1 ≤ (1 + (p.blockEnd (j - 1) : ℝ)) *
      (p.q (p.blockEnd (j - 1)) : ℝ) :=
    one_le_mul_of_one_le_of_one_le (by linarith) hq
  unfold ell
  constructor
  · positivity
  · apply one_div_le_one_div_of_le hj
    nlinarith

theorem tendsto_ell_zero : Tendsto p.ell atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    (tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_atTop_nhds_zero_nat
  have hsq : Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div_pow, zero_pow (by decide : 2 ≠ 0)] using h.pow 2
  exact squeeze_zero (fun n => (hp.ell_nonneg_and_le n).1)
    (fun n => (hp.ell_nonneg_and_le n).2) hsq

theorem samplingGraphAverage_ae_dist_lt
    (j : ℕ) (hj : 1 ≤ j) (r : ℕ)
    (hr : r < p.q (p.blockEnd (j - 1))) (t : Circle)
    (hshift : (p.shift j r : Circle) = t) :
    ∀ᵐ z ∂p.samplingGraphAverage θ j r, dist z.2 (z.1 + t) < p.ell j := by
  filter_upwards [p.samplingGraphAverage_ae_graph θ j r] with z hz
  obtain ⟨k, hk, heq⟩ := hz
  have hphase := (hp.samples_phase j hj r hr k hk).2
  rw [heq]
  change dist (z.1 + (((k : ℝ) * θ : ℝ) : Circle)) (z.1 + t) < p.ell j
  rw [dist_add_left, ← hshift, dist_eq_norm, ← AddCircle.coe_sub]
  calc
    ‖(((k : ℝ) * θ - p.shift j r : ℝ) : Circle)‖ =
        ‖((Int.fract ((k : ℝ) * θ - p.shift j r) : ℝ) : Circle)‖ := by
      rw [AddCircle.coe_fract]
    _ ≤ ‖Int.fract ((k : ℝ) * θ - p.shift j r)‖ := QuotientAddGroup.norm_mk_le_norm
    _ = Int.fract ((k : ℝ) * θ - p.shift j r) :=
      Real.norm_of_nonneg (Int.fract_nonneg _)
    _ < p.ell j := hphase

theorem tendsto_samplingGraph_translation_trimmed
    (j r : ℕ → ℕ) (hj : ∀ n, 1 ≤ j n)
    (hr : ∀ n, r n < p.q (p.blockEnd (j n - 1)))
    (hjt : Tendsto j atTop atTop) (t : Circle)
    (hshift : ∀ n, (p.shift (j n) (r n) : Circle) = t)
    (s : ℕ → Set Circle) (hs : ∀ n, MeasurableSet (s n))
    (hbase : Tendsto (fun n => circleMeasure.real (s n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => (p.samplingGraphFinite θ (j n) (r n) (hp.m_pos _ (hj n))).restrict
      (Prod.fst ⁻¹' s n)) atTop (𝓝 (circleFiniteBase.map (fun x => (x, x + t)))) := by
  apply GraphMeasureConvergence.tendsto_trimmed_graph_of_uniform_first_marginal
    _ circleFiniteBase (fun x => x + t) (continuous_id.add continuous_const)
    (hp.tendsto_samplingGraph_first_marginal j r hj hr hjt) _
    (hp.samplingGraph_marginals_uniformlyAbsolutelyContinuous j r hj hr).1 s hs hbase
  intro δ hδ
  filter_upwards [(hp.tendsto_ell_zero.comp hjt).eventually_lt_const hδ] with n hn
  exact (hp.samplingGraphAverage_ae_dist_lt (j n) (hj n) (r n) (hr n) t (hshift n)).mono
    (fun _ hz => hz.trans hn)

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Sampling_TrimmedCircleSamplingGraph
attribute [-instance] _root_.OAI.Invariant233.CircleParameterData.circleFiniteBase_probability _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
namespace Invariant233.CircleParameterData

theorem samplingDensity_false_eq_orbitGraphDensity (p : CircleParameterData)
    (θ : ℝ) (j n : ℕ) (x : Circle) :
    p.samplingDensity θ j n false x = p.orbitGraphDensity θ j n x := by
  simp only [samplingDensity, orbitGraphDensity, orientedKernel,
    Bool.false_eq_true, ↓reduceIte]

theorem samplingGraphAverage_ae_fst (p : CircleParameterData) (θ : ℝ)
    (j r : ℕ) (hm : 0 < p.m j) {P : Circle → Prop}
    (hP : ∀ᵐ x ∂circleMeasure, P x) :
    ∀ᵐ xy ∂p.samplingGraphAverage θ j r, P xy.1 := by
  apply ae_of_ae_map measurable_fst.aemeasurable
  rw [p.samplingGraphAverage_first_marginal θ j r hm]
  exact (withDensity_absolutelyContinuous _ _).ae_le hP

theorem trimmedSamplingGraphAverage_ae_good (p : CircleParameterData) (θ : ℝ)
    (A j r : ℕ) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j r,
      xy.1 ∈ p.rationalGraphGood A j :=
  ae_restrict_mem ((p.measurableSet_rationalGraphGood A j).preimage measurable_fst)

theorem trimmedSamplingGraphAverage_ae_density_graph (p : CircleParameterData)
    (θ : ℝ) (A j r : ℕ) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j r,
      ∃ n ∈ p.samples j r, 0 < p.orbitGraphDensity θ j n xy.1 ∧
        xy.2 = samplingTranslation θ n xy.1 := by
  have h := ae_restrict_of_ae (s := Prod.fst ⁻¹' p.rationalGraphGood A j)
    (p.samplingGraphAverage_ae_positive_density_graph θ j r)
  simpa only [trimmedSamplingGraphAverage, samplingDensity_false_eq_orbitGraphDensity] using h

end Invariant233.CircleParameterData

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem trimmedSamplingGraphAverage_ae_ratio_cap {A j r : ℕ}
    (hA : 1 ≤ A) (hj : 1 ≤ j) (hr : r < p.q (p.blockEnd (j - 1)))
    (ht : p.q A • ((p.shift j r : ℝ) : Circle) = 0) :
    ∀ᵐ xy ∂p.trimmedSamplingGraphAverage θ A j r,
      ∀ v : ℤ, p.floorCocycle θ v xy.2 / p.floorCocycle θ v xy.1 ≤
        Real.exp (p.rationalGraphPrefixCost A) := by
  obtain ⟨s, hs, hfull, hinv, hcap⟩ := hp.exists_uniform_rationalGraph_cap_set
  have hstart := ae_restrict_of_ae (s := Prod.fst ⁻¹' p.rationalGraphGood A j)
    (p.samplingGraphAverage_ae_fst θ j r (hp.m_pos j hj) hfull)
  filter_upwards [hstart, p.trimmedSamplingGraphAverage_ae_good θ A j r,
    p.trimmedSamplingGraphAverage_ae_density_graph θ A j r] with xy hx hg hd
  obtain ⟨n, hn, hpos, he⟩ := hd
  rw [he]
  exact hcap A j n hA hj xy.1 hx hg (p.shift j r) ht
    (hp.samples_phase j hj r hr n hn).2
    (hp.samples_range j hj r hr n hn).2 hpos.ne'

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Rotation_CircleRationalGraphApproximants
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.Rotation.circleMeasure_probability _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.isClosed_jointEigenspace _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
attribute [-simp] _root_.OAI.Invariant233.LaurentWindow.coeff_mul_T _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_nat _root_.OAI.Invariant233.LaurentWindow.coeff_toLaurent_neg _root_.OAI.Invariant233.LaurentWindow.coeff_trunc _root_.OAI.Invariant233.LaurentWindow.coeff_trunc_mul_T
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped Topology

namespace Invariant233.CircleParameterLaws
open CircleParameterData
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem rationalSamplingLabel_lt (A : ℕ) (r : ℤ) (n : ℕ) :
    hp.rationalSamplingLabel A r n < p.q (p.blockEnd (rationalSamplingStage A n - 1)) :=
  (Classical.choose_spec (hp.exists_rational_sampling_index_of_late
    (A := A) (j := rationalSamplingStage A n) (by unfold rationalSamplingStage; omega) r)).1

theorem rationalSamplingLabel_shift (A : ℕ) (r : ℤ) (n : ℕ) :
    (p.shift (rationalSamplingStage A n) (hp.rationalSamplingLabel A r n) : Circle) =
      p.rationalTranslation A r :=
  (Classical.choose_spec (hp.exists_rational_sampling_index_of_late
    (A := A) (j := rationalSamplingStage A n) (by unfold rationalSamplingStage; omega) r)).2.symm

theorem rationalSamplingStage_tendsto (A : ℕ) :
    Tendsto (rationalSamplingStage A) atTop atTop := by
  exact tendsto_atTop_mono (fun n => by dsimp [rationalSamplingStage]; omega) tendsto_id

theorem rationalGraphApproximant_tendsto (A : ℕ) (hA : 1 ≤ A) (r : ℤ) :
    Tendsto (hp.rationalGraphApproximant A r) atTop
      (𝓝 (circleTranslationGraph (p.rationalTranslation A r))) := by
  have hb : Tendsto (fun n => circleMeasure.real
      (p.rationalGraphGood A (rationalSamplingStage A n))ᶜ) atTop (𝓝 0) := by
    have hshift : Tendsto (fun n : ℕ => n + A) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right n A) tendsto_id
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
      ((hp.tendsto_measure_rationalGraphBad hA).comp hshift)
    simpa only [rationalSamplingStage, rationalGraphBad, Measure.real,
      Function.comp_def, ENNReal.toReal_zero] using h
  have h := hp.tendsto_samplingGraph_translation_trimmed
    (rationalSamplingStage A) (hp.rationalSamplingLabel A r)
    (rationalSamplingStage_pos A) (hp.rationalSamplingLabel_lt A r)
    (rationalSamplingStage_tendsto A) (p.rationalTranslation A r)
    (hp.rationalSamplingLabel_shift A r)
    (fun n => p.rationalGraphGood A (rationalSamplingStage A n))
    (fun n => p.measurableSet_rationalGraphGood A _) hb
  exact h

theorem rationalGraphApproximant_marginals (A : ℕ) (r : ℤ) :
    UniformlyAbsolutelyContinuous circleMeasure
      (fun n => (hp.rationalGraphApproximant A r n : Measure (Circle × Circle)).map Prod.fst) ∧
    UniformlyAbsolutelyContinuous circleMeasure
      (fun n => (hp.rationalGraphApproximant A r n : Measure (Circle × Circle)).map Prod.snd) := by
  obtain ⟨hfirst, hsecond⟩ := hp.samplingGraph_marginals_uniformlyAbsolutelyContinuous
    (rationalSamplingStage A) (hp.rationalSamplingLabel A r)
    (rationalSamplingStage_pos A) (hp.rationalSamplingLabel_lt A r)
  exact ⟨hfirst.map_restrict Prod.fst measurable_fst _,
    hsecond.map_restrict Prod.snd measurable_snd _⟩

theorem rationalGraphApproximant_positive_orbits (A : ℕ) (r : ℤ) (n : ℕ) :
    ∀ᵐ z ∂(hp.rationalGraphApproximant A r n : Measure (Circle × Circle)),
      ∃ k : ℕ, 0 < k ∧ z.2 = CircleWeights.rotate θ (k : ℤ) z.1 := by
  have h := ae_restrict_of_ae (s := Prod.fst ⁻¹'
      p.rationalGraphGood A (rationalSamplingStage A n))
    (hp.samplingGraphAverage_ae_positive_graph (rationalSamplingStage A n)
      (rationalSamplingStage_pos A n) (hp.rationalSamplingLabel A r n)
      (hp.rationalSamplingLabel_lt A r n))
  filter_upwards [h] with z hz
  obtain ⟨k, _, hk, he⟩ := hz
  refine ⟨k, hk, ?_⟩
  simpa only [samplingTranslation, CircleWeights.rotate, natCast_zsmul,
    ← AddCircle.coe_nsmul, nsmul_eq_mul] using he

theorem rationalGraphApproximant_ratio_cap (A : ℕ) (hA : 1 ≤ A) (r : ℤ)
    (n : ℕ) :
    ∀ᵐ z ∂(hp.rationalGraphApproximant A r n : Measure (Circle × Circle)),
      ∀ v : ℤ, p.floorCocycle θ v z.2 / p.floorCocycle θ v z.1 ≤
        p.rationalRatioBound A := by
  have ht : p.q A • ((p.shift (rationalSamplingStage A n)
      (hp.rationalSamplingLabel A r n) : ℝ) : Circle) = 0 := by
    rw [hp.rationalSamplingLabel_shift A r n]
    simpa only [rationalTranslation, Int.cast_natCast, natCast_zsmul] using
      CircleCharacterDynamics.zsmul_rational_eq_zero
        (q := (p.q A : ℤ)) (d := (p.q A : ℤ))
        (by exact_mod_cast (hp.q_pos A).ne') dvd_rfl r
  exact hp.trimmedSamplingGraphAverage_ae_ratio_cap hA
    (rationalSamplingStage_pos A n) (hp.rationalSamplingLabel_lt A r n) ht

include hp

theorem rationalGraphIdentities_of_positive_orbits
    (P : Circle → SequenceHilbert ℤ →L[ℂ] SequenceHilbert ℤ)
    (hP : ∀ x, IsStarProjection (P x))
    (hPm : ∀ k : ℤ, Measurable (fun x => P x (lp.single 2 k 1)))
    (horbit : ∀ n : ℕ, 0 < n → ∀ᵐ x ∂circleMeasure,
      (1 - P (CircleWeights.rotate θ (n : ℤ) x)).comp
        ((ratioDiagonal (p.floorCocycle θ)
          (x, CircleWeights.rotate θ (n : ℤ) x)).comp (P x)) = 0) :
    p.RationalGraphIdentities θ P := by
  apply hp.rationalGraphIdentities_of_forall P
  intro A hA r
  apply hp.rational_graph_identity_of_orbit_approximants P hP hPm horbit A hA r
    (hp.rationalGraphApproximant A r) (hp.rationalGraphApproximant_tendsto A hA r)
    (hp.rationalGraphApproximant_marginals A r).1
    (hp.rationalGraphApproximant_marginals A r).2
  · intro n k
    exact (hp.rationalGraphApproximant_ratio_cap A hA r n).mono fun _ h => h k
  · exact hp.rationalGraphApproximant_positive_orbits A r

end Invariant233.CircleParameterLaws

end

end OAI
end

section
-- module Solutions.Q234_IR.IrrationalRotation_Analysis_RationalGraphs
attribute [-instance] _root_.OAI.Invariant233.OneCoordinateCoupling.labelMeasurableSpace _root_.OAI.Invariant233.OrderedProductCoupling.circlePairLaw_probability _root_.OAI.Invariant233.ProductModel.IdealSampling.law_finite _root_.OAI.Invariant233.ProductModel.IdealSampling.sourceMeasure_finite _root_.OAI.Invariant233.ProductModel.baseMeasure_probability _root_.OAI.Invariant233.ProductModel.instCompleteSpaceHilbertCounterexample _root_.OAI.Invariant233.ProductModel.prefixPairLaw_finite _root_.OAI.Invariant233.TrialSampling.spatialLaw_probability _root_.OAI.Invariant233.WeightedShift.SpectralCutoff.cutoffSpace_hasOrthogonalProjection _root_.OAI.Invariant233.circleMeasure_probability _root_.OAI.Invariant233.vonNeumannNormClosed _root_.OAI.Invariant233.vonNeumannSMulMemClass _root_.OAI.Invariant233.ProjectionMeetTrace.inf_complete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory

namespace Invariant233.CircleParameterLaws
variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)

theorem exists_rational_graph_field_oai
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (hmem : P ∈ Rotation.algebra θ) (hP : IsStarProjection P)
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0) :
    ∃ F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber,
      (∀ x, IsStarProjection (F x)) ∧
      (∀ x, ‖F x‖ ≤ ‖P‖) ∧
      (∀ v : Rotation.Fiber, StronglyMeasurable fun x => F x v) ∧
      (∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun x => F x (ξ x)) ∧
      p.RationalGraphIdentities θ F := by
  obtain ⟨F, hproj, hnorm, hmeas, hrep, _, horbit⟩ :=
    hp.exists_measurableOperator_positive_orbit_field hmem hP hT
  refine ⟨F, hproj, hnorm, hmeas, hrep, ?_⟩
  apply hp.rationalGraphIdentities_of_positive_orbits F hproj
    (fun k => (hmeas (lp.single 2 k 1)).measurable)
  intro n hn
  filter_upwards [horbit] with x hx
  exact hx n

end Invariant233.CircleParameterLaws

end

end OAI
end

theorem solution : type_of% @OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_oai := @OAI.Invariant233.CircleParameterLaws.exists_rational_graph_field_oai
